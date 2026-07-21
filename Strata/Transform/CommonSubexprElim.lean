/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Strata.Util.List
public import Strata.Util.PtrCache
import Lean.Util.ShareCommon

/-! # Common Subexpression Elimination

Core-to-Core transformation that extracts common subexpressions into fresh
`var` declarations, reducing duplicated subexpressions from partially evaluated
result.

For example:
```
assume F(2+z) >= 5
assert F(2+z)+F(2+z) == 2*F(2+z)
```
becomes:
```
// Note that 2+z is not deduplicated even if it appeared four times in the
// original code.

var $__cse.0 := F(2+z)
assume $__cse.0 >= 5
assert $__cse.0+$__cse.0 == 2*$__cse.0
```

The pass walks procedure bodies via `runCSE`, hoisting duplicated
subexpressions into `var` declarations prepended to the body.
-/

public section

namespace Core.CSE

open Lambda Imperative

/-- Prefix used for CSE-generated variable names. Shared between the encoder
    and the verifier's model filter. -/
def cseVarPrefix : String := "$__cse."

open Strata.PtrCache

abbrev hx : Expression.Expr → UInt64 := LExpr.hashExpr

---------------------------------------------------------------------
-- Subexpression hashes calculator
---------------------------------------------------------------------

/-- Monadic structural hash: threads the shared `PtrCache` (the state monad's
    state) and returns the memoized structural hash of `e`. O(1) for a node that
    was already hashed. -/
private def hashM (e : Expression.Expr) : StateM (PtrCache hx) UInt64 := do
  return (← evalPtrCache e (LExpr.hashExprPtrCache e)).output

/-- Collect the hashes of every proper subexpression of `e` into `acc`.
    `top := true` marks a top-level candidate, whose own hash is not
    recorded. -/
private def collectSubexprHashes (acc : Std.HashSet UInt64) (top : Bool)
    (e : Expression.Expr) : StateM (PtrCache hx) (Std.HashSet UInt64) := do
  let he ← hashM e
  if !top && acc.contains he then return acc
  else
    let acc := if top then acc else acc.insert he
    match e with
    | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => return acc
    | .app _ fn arg =>
      let acc ← collectSubexprHashes acc false fn
      collectSubexprHashes acc false arg
    | .ite _ c t f =>
      let acc ← collectSubexprHashes acc false c
      let acc ← collectSubexprHashes acc false t
      collectSubexprHashes acc false f
    | .eq _ e1 e2 =>
      let acc ← collectSubexprHashes acc false e1
      collectSubexprHashes acc false e2
    | .abs _ _ _ body => collectSubexprHashes acc false body
    | .quant _ _ _ _ tr body =>
      let acc ← collectSubexprHashes acc false tr
      collectSubexprHashes acc false body
  termination_by e

/-- Remove entries that are subexpressions of larger entries in the list,
    keeping only the maximal ones. -/
private def removeSubsumed (memo : PtrCache hx)
    (exprs : List Expression.Expr) : List Expression.Expr :=
  let (subHashes, memo) :=
    (exprs.foldlM (fun acc e => collectSubexprHashes acc true e)
      ({} : Std.HashSet UInt64)).run memo
  exprs.filter (fun e => !subHashes.contains ((hashM e).run' memo))


---------------------------------------------------------------------
-- Common subexpressions finder
---------------------------------------------------------------------

/-- Traversal state.
    * `memoHash` caches each visited node's structural hash by pointer identity.
    * `seen` records visited LExprs. Maps hash to the distinct subexpressions carrying it;
    * `dups` is the subset of `seen` encountered at least twice. -/
private structure CollectedExprs where
  memoHash : PtrCache hx := PtrCache.empty
  seen : Std.HashMap UInt64 (Array Expression.Expr) := {}
  dups : Std.HashMap UInt64 (Array Expression.Expr) := {}

/-- Record the first occurrence of a bvar-free `e` in `seen` under hash `h`. -/
private def CollectedExprs.recordSeen (st : CollectedExprs) (h : UInt64)
    (e : Expression.Expr) : CollectedExprs :=
  { st with seen := st.seen.insert h ((st.seen.getD h #[]).push e) }

/-- Structural equality with a safe pointer-equality fast path. -/
private def exprEq (a b : Expression.Expr) : Bool :=
  match withPtrEqDecEq a b (fun _ => (inferInstance : DecidableEq Expression.Expr) a b) with
  | isTrue _ => true
  | isFalse _ => false

/-- Note a repeated occurrence: add `e` to the `dups` bucket for `h` (once). -/
private def CollectedExprs.recordDup (st : CollectedExprs) (h : UInt64)
    (e : Expression.Expr) : CollectedExprs :=
  let bucket := st.dups.getD h #[]
  -- The performance of the code below relies on an assumption that there is
  -- almost no hash collision; hence bucket.size is either 0 or 1.
  if bucket.any (exprEq e) then st
  else { st with dups := st.dups.insert h (bucket.push e) }

/-- Structural hash of `e` (O(1) once cached), threading the shared `PtrCache`
    held in the `memoHash` field. -/
private def CollectedExprs.withHash (st : CollectedExprs) (e : Expression.Expr) :
    UInt64 × CollectedExprs :=
  let (r, memoHash) := (evalPtrCache e (LExpr.hashExprPtrCache e)).run st.memoHash
  (r.output, { st with memoHash })

/-- Walk `e` and record every eligible subexpression into `st`.
    A subexpression is eligible when it is a non-leaf.
    For function applications, records the full (curried) application and
    recurses into each argument, but does not record intermediate partial
    applications from the spine. `abs` bodies contribute nothing but
    still propagate their bvar-free flag to the parent.

    The returned `Bool` is `true` when `e` is bvar-free. The node's hash is
    computed once at the top via the pointer-memoized `hashCached`, so the
    `seen` early-return costs O(1) rather than an O(tree) rehash. -/
private def collectSubexprs (st : CollectedExprs) (e : Expression.Expr) :
    Bool/- is `e` bvar-free? -/ × CollectedExprs :=
  let (h, st) := st.withHash e
  -- Early exit on a subexpression we have already fully traversed. Everything
  -- recorded in `seen` was inserted on the bvar-free branch, so a hit means
  -- `e` is bvar-free and its subexpressions were already recorded on the first
  -- encounter; we only bump its duplicate count.
  if (st.seen.getD h #[]).any (exprEq e) then
    (true, st.recordDup h e)
  else
  match e with
  | .const _ _ | .fvar _ _ _ | .op _ _ _ => (true, st)
  | .bvar _ _ => (false, st)
  | .app _ fn arg =>
    let (fnOk, st) := walkSpine st fn
    let (argOk, st) := collectSubexprs st arg
    let ok := fnOk && argOk
    (ok, if ok then st.recordSeen h e else st)
  | .ite _ c t f =>
    let (cOk, st) := collectSubexprs st c
    let (tOk, st) := collectSubexprs st t
    let (fOk, st) := collectSubexprs st f
    let ok := cOk && tOk && fOk
    (ok, if ok then st.recordSeen h e else st)
  | .eq _ e1 e2 =>
    let (ok1, st) := collectSubexprs st e1
    let (ok2, st) := collectSubexprs st e2
    let ok := ok1 && ok2
    (ok, if ok then st.recordSeen h e else st)
  | .abs _ _ _ body =>
    -- Report bvar-freeness (may spuriously return true because it doesn't
    -- compare de bruijn index with the depth) through the body so a parent
    -- sees the flag, but do not record subexpressions under the binder.
    (!body.hasBVar, st)
  | .quant _ _ _ _ tr body =>
    let (ok1, st1) := collectSubexprs st tr
    let (ok2, st2) := collectSubexprs { st with memoHash := st1.memoHash } body
    (ok1 && ok2, { st with memoHash := st2.memoHash })
where
  /-- Walk an application spine: recurse into each argument via
      `collectSubexprs`, but do not record the intermediate partial
      applications (matches the original behavior). Threads the bvar-free flag
      through the spine head so the enclosing `.app` sees it. In practice
      spine heads in Core IR are always `.app`/`.op`/`.fvar`/`.const`; the
      catch-all fallback preserves correctness for the rare exotic case
      (e.g. `(if ... then f else g) x`). -/
  walkSpine (st : CollectedExprs) (e : Expression.Expr) : Bool × CollectedExprs :=
    match e with
    | .app _ fn arg =>
      let (fnOk, st) := walkSpine st fn
      let (argOk, st) := collectSubexprs st arg
      (fnOk && argOk, st)
    | .bvar _ _ => (false, st)
    | .const _ _ | .fvar _ _ _ | .op _ _ _ => (true, st)
    | e => (!e.hasBVar, st)

/-- Shared pipeline: walk the input expressions once to collect duplicate
    eligible subexpressions, remove subsumed entries. -/
private def collectExprsToAbbreviate (exprs : List Expression.Expr) :
    List Expression.Expr :=
  let final := exprs.foldl (fun st e => (collectSubexprs st e).2) ({} : CollectedExprs)
  let duplicates := (final.dups.toList.mergeSort (fun a b => a.1 < b.1)).flatMap
    (fun (_, bucket) => bucket.toList)
  removeSubsumed final.memoHash duplicates

---------------------------------------------------------------------
-- Fast replacement of subexpressions
---------------------------------------------------------------------

/-- A memoized rewrite of one node: the `original` expression, its structural
    `hash`, and its `rewritten` form. Bucketed by `hash`, kept collision-safe by
    an `exprEq` guard on `original`. -/
private structure Rewrite where
  original  : Expression.Expr
  originalHash : UInt64
  rewritten : Expression.Expr

/-- Traversal state for `replaceExprs`: the shared structural-hash `PtrCache`
    plus the rewrite memo (bucketed by original-node hash). -/
private structure RwState where
  cache : PtrCache hx := PtrCache.empty
  memo  : Std.HashMap UInt64 (List Rewrite) := {}

/-- Structural hash of `e` (O(1) once cached), threading the shared cache held
    in the `RwState`. -/
private def RwState.hashM (e : Expression.Expr) : StateM RwState UInt64 := do
  let s ← get
  let (r, cache) := (evalPtrCache e (LExpr.hashExprPtrCache e)).run s.cache
  set { s with cache }
  return r.output

/-- Rewrite the (already-rebuilt) node `e` if it matches a replacement target
    under hash `h`; otherwise return it unchanged. -/
private def tryReplace
    (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (h : UInt64) (e : Expression.Expr) : UInt64 × Expression.Expr :=
  match replacements[h]? with
  | some pairs =>
    match pairs.find? (fun (t, _) => exprEq e t) with
    | some (_, replacement) => (h, replacement)
    | none => (h, e)
  | none => (h, e)

/-- Bottom-up rewrite of `e`, returning its (rewritten) structural hash and its
    rewritten form. Each node's result is memoized in `RwState.memo`, keyed by
    the original node's structural hash (O(1) from the shared `PtrCache`) and
    made collision-safe by an `exprEq` guard on the stored original. -/
private def replaceSubexprs
    (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) : StateM RwState (UInt64 × Expression.Expr) := do
  let ho ← RwState.hashM e
  let s ← get
  match (s.memo.getD ho []).find? (fun r => exprEq r.original e) with
  | some r => return (r.originalHash, r.rewritten)
  | none =>
    let check := tryReplace replacements
    let (h, e') ← match e with
      | .const _ c => pure (check (LExpr.hashConst (hash c)) e)
      | .bvar _ i => pure (check (LExpr.hashBVar (hash i)) e)
      | .fvar _ n ty => pure (check (LExpr.hashFVar (hash n.name) (LExpr.hashOptTy ty)) e)
      | .op _ o ty => pure (check (LExpr.hashOp (hash o.name) (LExpr.hashOptTy ty)) e)
      | .app m fn arg =>
        let (hfn, fn') ← replaceSubexprs replacements fn
        let (harg, arg') ← replaceSubexprs replacements arg
        pure (check (LExpr.hashApp hfn harg) (.app m fn' arg'))
      | .ite m c t f =>
        let (hc, c') ← replaceSubexprs replacements c
        let (ht, t') ← replaceSubexprs replacements t
        let (hf, f') ← replaceSubexprs replacements f
        pure (check (LExpr.hashIte hc ht hf) (.ite m c' t' f'))
      | .eq m e1 e2 =>
        let (h1, e1') ← replaceSubexprs replacements e1
        let (h2, e2') ← replaceSubexprs replacements e2
        pure (check (LExpr.hashEqExpr h1 h2) (.eq m e1' e2'))
      | .abs m name ty body =>
        let (hbody, body') ← replaceSubexprs replacements body
        pure (check (LExpr.hashAbs (hash name) (LExpr.hashOptTy ty) hbody) (.abs m name ty body'))
      | .quant m k name ty tr body =>
        let (htr, tr') ← replaceSubexprs replacements tr
        let (hbody, body') ← replaceSubexprs replacements body
        let kh : UInt64 := match k with | .all => 0 | .exist => 1
        pure (check (LExpr.hashQuantExpr kh (hash name) (LExpr.hashOptTy ty) htr hbody)
                (.quant m k name ty tr' body'))
    modify fun s => { s with memo := s.memo.insert ho (⟨e, h, e'⟩ :: s.memo.getD ho []) }
    return (h, e')
  termination_by e

/-- Apply subexpression replacement to `e`. -/
private def replaceExprs
    (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) : Expression.Expr :=
  ((replaceSubexprs replacements e).run' {}).2

---------------------------------------------------------------------
-- Program level common subexpression elimination
---------------------------------------------------------------------

/-- Fuel for `stmtRunCSE`'s fixpoint loop.
    The loop exits early once nothing more can be extracted. -/
def fuel : Nat := 1024

/-- A single common-subexpression-elimination iteration. Extracts the maximal
    duplicated subexpressions of `body` into fresh `var` declarations (fresh
    indices starting at `startIdx`), rewrites the body to reference them, and
    prepends the declarations. Returns `none` when there is nothing to extract. -/
def stmtRunCSEIter (body : Statements) (startIdx : Nat) : Option (Statements × Nat) :=
  let targets := collectExprsToAbbreviate (Statements.collectExprs body)
  if targets.isEmpty then
    none
  else
    -- Build all var declarations and the replacement map. The map value is a
    -- list of (target, replacement) pairs to be collision-safe under the
    -- structural hash; see `replaceExprs` above.
    let (revDecls, replacements, nextIdx) := targets.foldl (fun (decls, repMap, idx) dup =>
      let freshName : CoreIdent := ⟨s!"{cseVarPrefix}{idx}", ()⟩
      let freshTy := dup.typeOf
      let freshVar : Expression.Expr := .fvar () freshName freshTy
      let ty : Expression.Ty := match freshTy with
        | some mty => LTy.forAll [] mty
        | none => LTy.forAll ["α"] (.ftvar "α")
      let varDecl := Statement.init freshName ty (.det dup) .empty
      let h := LExpr.hashExprCached dup
      let pairs := repMap.getD h []
      (varDecl :: decls, repMap.insert h ((dup, freshVar) :: pairs), idx + 1)
    ) ([], ({} : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr))), startIdx)
    let body' := Statements.mapExprs (replaceExprs replacements) body
    -- `reverseAux` reverses `revDecls` onto `body'` in a single pass, avoiding
    -- the intermediate list that `revDecls.reverse ++ body'` would allocate.
    some (revDecls.reverseAux body', nextIdx)

/-- Deduplicate a procedure's body by extracting common subexpressions into
    `var` declarations prepended to the body. Returns the modified body and
    the next available dedup index. -/
def stmtRunCSE (body : Statements) (startIdx : Nat) : Statements × Nat :=
  -- For performance, maximize structural sharing of subexpressions up front, so
  -- the pointer-address hash cache hashes each distinct subterm exactly once
  -- (and `exprEq`'s pointer fast path hits more often).
  go fuel (Lean.ShareCommon.shareCommon body) startIdx
where
  go (steps : Nat) (body : Statements) (startIdx : Nat) : Statements × Nat :=
    match steps with
    | 0 => (body, startIdx)
    | steps' + 1 =>
      match stmtRunCSEIter body startIdx with
      | none => (body, startIdx)
      | some (newBody, nextIdx) => go steps' newBody nextIdx

/-- Deduplicate all procedures in a program. Returns the modified program
    and whether any changes were made. -/
def runCSE (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  let (revDecls, _, changed) := p.decls.foldl (fun (acc, idx, changed) decl =>
    match decl with
    | .proc proc md =>
      match proc.body with
      | .structured ss =>
        let (body', idx') := stmtRunCSE ss idx
        (.proc { proc with body := .structured body' } md :: acc, idx', changed || idx' > idx)
      | .cfg _ =>
        -- CFG bodies are not transformed by CSE for now.
        (.proc proc md :: acc, idx, changed)
    | other => (other :: acc, idx, changed)
  ) ([], 0, false)
  return (changed, { decls := revDecls.reverse })

end Core.CSE

/-- CSE pipeline phase: extracts common subexpressions into fresh
    variable declarations. Model-preserving because it only introduces
    definitional equalities without changing program semantics. -/
def Core.commonSubexprElimPhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "CommonSubexprElim" Core.CSE.runCSE

end -- public section
