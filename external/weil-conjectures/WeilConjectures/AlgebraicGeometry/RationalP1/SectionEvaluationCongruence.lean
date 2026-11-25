/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Lean.Meta.CongrTheorems
/-! # Checked structural congruence for coefficient instances -/
@[expose] public section
set_option autoImplicit false
universe u₁ u₂
namespace AlgebraicGeometry.ProEtale.RationalP1
/- The structural instance comparison follows the proved congruence procedure in
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
(G3). All produced terms are built from HEq reflexivity, proof irrelevance, function
extensionality and congruence theorems. -/
/-- Equality of dependent function types under heterogeneous equality of families. -/
theorem sectionEvaluationPiEq {α β : Sort u₁} {P : α → Sort u₂}
    {Q : β → Sort u₂} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

open Lean Meta Elab Tactic in
private meta structure CoefficientCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

open Lean Meta Elab Tactic in
private meta partial def coefficientHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT CoefficientCongrState MetaM Expr := do
  if lhs == rhs then return ← mkHEqRefl lhs
  for (a, b, h) in (← get).proofs do
    if a == lhs && b == rhs then return h
  if fuel == 0 then throwError "coefficient congruence exhausted: {lhs}
{rhs}"
  let next := fuel - 1
  let prove : StateRefT CoefficientCongrState MetaM Expr := do
    if (← isProof lhs) && (← isProof rhs) then
      return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
    match lhs, rhs with
    | .lam n α body _, .lam _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let init ← get
      let hfun ← withLocalDeclD n α fun x =>
        withLocalDeclD (n.appendAfter "'") β fun y => do
        withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
          modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
          let h ← coefficientHEq (body.instantiate1 x) (body'.instantiate1 y) next
          mkLambdaFVars #[x, y, hxy] h
      let congrs := (← get).congrs
      set { init with congrs := congrs }
      let ty ← whnf (← inferType lhs)
      let ty' ← whnf (← inferType rhs)
      let P := mkLambda n .default α ty.bindingBody!
      let Q := mkLambda n .default β ty'.bindingBody!
      return ← mkAppOptM ``Function.hfunext #[some α, some β, some P, some Q,
        some lhs, some rhs, some hα, some hfun]
    | .forallE n α body _, .forallE _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let P := mkLambda n .default α body
      let Q := mkLambda n .default β body'
      let hPQ ← coefficientHEq P Q next
      let h ← mkAppOptM ``sectionEvaluationPiEq #[some α, some β, some P, some Q,
        some hα, some hPQ]
      return ← mkHEqOfEq h
    | _, _ => pure ()
    let expandProjection (e : Expr) : MetaM Expr := do
      let .proj typeName index major := e.getAppFn | return e
      let info := Lean.getStructureInfo (← getEnv) typeName
      let p ← mkProjection major info.fieldNames[index]!
      return mkAppN p e.getAppArgs
    let lhs' ← expandProjection lhs
    let rhs' ← expandProjection rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if f == g && xs.size == ys.size && !xs.isEmpty then
      let init ← get
      try
        let mut found := none
        for (ff, arity, thm) in (← get).congrs do
          if ff == f && arity == xs.size then found := some thm
        let thm? ← match found with
          | some thm => pure (some thm)
          | none => do
            let thm? ← if let .const name levels := f then
              mkHCongrWithArityForConst? name levels xs.size
            else
              try pure (some (← mkHCongrWithArity f xs.size))
              catch _ => pure none
            if let some thm := thm? then
              modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
            pure thm?
        if let some thm := thm? then
          let mut args := #[]
          for i in [:xs.size] do
            let h ← coefficientHEq xs[i]! ys[i]! next
            let h ← if thm.argKinds[i]! == .eq then mkEqOfHEq h else pure h
            args := args ++ #[xs[i]!, ys[i]!, h]
          let h := mkAppN thm.proof args
          let ty ← inferType h
          if ty.isHEq then return h else return ← mkHEqOfEq h
        else
          let ty ← whnf (← inferType lhs)
          let ty' ← whnf (← inferType rhs)
          if ty.isForall && ty'.isForall then
            let lhs' := mkLambda ty.bindingName! .default ty.bindingDomain!
              (mkApp (lhs.liftLooseBVars 0 1) (.bvar 0))
            let rhs' := mkLambda ty'.bindingName! .default ty'.bindingDomain!
              (mkApp (rhs.liftLooseBVars 0 1) (.bvar 0))
            return ← coefficientHEq lhs' rhs' next
      -- Some wrappers ignore parameters. If argumentwise congruence fails, unfold
      -- the wrapper below and compare its values instead.
      catch _ => set init
    let lhs' ← whnf lhs
    let rhs' ← whnf rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let lhs' := (← unfoldDefinition? lhs).getD lhs
    let rhs' := (← unfoldDefinition? rhs).getD rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    throwError "coefficient congruence stuck:
{lhs}
{rhs}"
  let h ← prove
  modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
  return h

open Lean Meta Elab Tactic in
elab "section_evaluation_exact " t:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let val ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let val ← instantiateMVars val
  let actual ← inferType val
  let (h, _) ← (coefficientHEq actual target).run {}
  let result ← mkAppM ``Eq.mp #[← mkEqOfHEq h, val]
  goal.assign result
  replaceMainGoal []

end AlgebraicGeometry.ProEtale.RationalP1
