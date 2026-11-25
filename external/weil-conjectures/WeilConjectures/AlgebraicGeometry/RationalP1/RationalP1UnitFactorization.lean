/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1SectionEvaluation
import Mathlib.Logic.Function.Basic
import Mathlib.Lean.Meta.CongrTheorems

/-! # Factoring the normalized projective-line unit
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison
attribute [local irreducible] twist projectionMap singleUnitIso
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientExchange

-- The private congruence builder follows FiniteCoefficientProperFormulaTools.
-- It emits kernel-checked congruences without reducing entire sheafification constructions.
private theorem coefficientPiEq {α β : Sort v} {P : α → Sort w}
    {Q : β → Sort w} (h : α = β) (hPQ : HEq P Q) :
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
      let h ← mkAppOptM ``coefficientPiEq #[some α, some β, some P, some Q,
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
private meta def coefficientCongrGoal : TacticM Unit := do
  liftMetaTactic fun goal => goal.withContext do
    let ty ← goal.getType
    let some (_, lhs, rhs) := ty.eq? | throwError "expected equality"
    let (h, _) ← (coefficientHEq lhs rhs).run {}
    goal.assign (← mkEqOfHEq h)
    return []

/-- The functorial calculation with an unbundled coefficient object. -/
private theorem unit_factorization_generic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (η : M ⟶ (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)))
    (hη : UnitComponentNormalized Λ Y L d e M η)
    :
    ∃ (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y))
      e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))),
    η = firstKernelInsertion Λ Y M
      (((DerivedCategory.singleFunctor
        (Modules Λ (diagonalSurface Y)) 0).obj
          (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      d.delta ≫
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules Λ (diagonalSurface Y)) 0).obj
              (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso Λ (diagonalSurface Y)
            (L (diagonalSurface Y))
            ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap Λ (secondProjection Y)
          (L (ProjectiveLine Y)) (L (diagonalSurface Y))
          e
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) hp ≫
        (twist Λ (ProjectiveLine Y)
          (L (ProjectiveLine Y))).map
          (by
            exact @inv _ _ _ _
              ((condensedAmbientExchange Λ (square Y)).app M) hb)) := by
  obtain ⟨hb, hp, h⟩ := hη
  refine ⟨hb, hp, ?_⟩
  refine (eq_of_heq h).trans ?_
  simp only [unitComponent, diagonalClassMap, firstKernelInsertion,
    Functor.map_comp, Category.assoc]

-- Fix the coefficient and all native endpoints before spelling out the unit paste.
/-- Factor the normalized unit into kernel insertion and the remaining inverse exchange paste.
No counit, trace functional, trace transport or integration equation occurs in this statement. -/
theorem rationalP1_unit_factorization
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (family : Family l Y)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (η : M ⟶ (twist (coefficient l c).X (ProjectiveLine Y)
      (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)))
    (hη : UnitComponentNormalized (coefficient l c).X Y (line l c) (diagram l c Y family)
      (secondLineComparison l c k p hpl Y) M η)
    :
    ∃ (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M))),
    η = firstKernelInsertion (coefficient l c).X Y M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      (diagram l c Y family).delta ≫
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
            (line l c (diagonalSurface Y))
            ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)) hp ≫
        (twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)) := by
  refine Eq.mp ?_ (unit_factorization_generic (coefficient l c).X Y (line l c)
    (diagram l c Y family) (secondLineComparison l c k p hpl Y) M η hη)
  run_tac coefficientCongrGoal

end AlgebraicGeometry.ProEtale.RationalP1
