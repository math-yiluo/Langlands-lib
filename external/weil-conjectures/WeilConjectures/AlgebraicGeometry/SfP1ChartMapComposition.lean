/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData

/-! # Direct-image composition in the projective-line chart

This is the definition-expansion step of the chart exchange argument.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

-- Compare recorded instances without expanding the derived localization constructions.
private meta def unfoldBoundary (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if let .fvar id := e then
    if let some v := (← id.getDecl).value? then return some v
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  let names : List Lean.Name := [``DerivedCategoryModule, ``ordinaryFinitePushforward,
    ``ordinaryFinitePullback, ``ordinaryFiniteP1DiagonalTarget,
    ``ordinaryFiniteP1DiagonalChartMap, ``ordinaryFiniteChartTransport,
    ``ordinaryFiniteAdjunction]
  if let some n := e.getAppFn.constName? then
    if names.contains n then
      return ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e)
  return none

private meta def reduceRecordProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  let some n := e.getAppFn.constName? | return none
  let some info ← Lean.getProjectionFnInfo? n | return none
  let args := e.getAppArgs
  unless args.size == info.numParams + 1 do return none
  let v ← Lean.Meta.withTransparency .all (Lean.Meta.whnf args.back!)
  Lean.Expr.reduceProjStruct? (Lean.mkAppN e.getAppFn (args.set! (args.size - 1) v))

private meta def reduceIdentityObj (e : Lean.Expr) : Lean.Expr := Id.run do
  if e.getAppFn.isConstOf ``Functor.obj then
    let args := e.getAppArgs
    if args.size ≥ 2 && (args[args.size - 2]!).getAppFn.isConstOf ``Functor.id then
      return args.back!
  return e

/-- Build a kernel-checked congruence, treating proof arguments by proof irrelevance. -/
private meta def structuralHEq : Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _ => throwError "chart congruence exhausted its structural depth"
  | fuel + 1, lhs, rhs => do
    let lhs := reduceIdentityObj (← Lean.instantiateMVars lhs).consumeMData.headBeta
    let rhs := reduceIdentityObj (← Lean.instantiateMVars rhs).consumeMData.headBeta
    if lhs == rhs then return ← Lean.Meta.mkHEqRefl lhs
    if let (.const n _, .const m _) := (lhs, rhs) then
      if n == m then return ← Lean.Meta.mkHEqRefl lhs
    if lhs.isSort && rhs.isSort && (← Lean.Meta.isDefEq lhs rhs) then
      return ← Lean.Meta.mkHEqRefl lhs
    if ← Lean.Meta.isProp (← Lean.Meta.inferType lhs) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
    let aa := lhs.getAppArgs
    let bb := rhs.getAppArgs
    let sameHead := lhs.getAppFn == rhs.getAppFn ||
      (lhs.getAppFn.constName?.isSome && lhs.getAppFn.constName? == rhs.getAppFn.constName?)
    unless sameHead && aa.size == bb.size && aa.size > 0 do
      if let some a ← unfoldBoundary lhs then return ← structuralHEq fuel a rhs
      if let some b ← unfoldBoundary rhs then return ← structuralHEq fuel lhs b
      if let some a ← reduceRecordProjection lhs then return ← structuralHEq fuel a rhs
      if let some b ← reduceRecordProjection rhs then return ← structuralHEq fuel lhs b
      if lhs.isLambda || rhs.isLambda then
        if ← Lean.Meta.isDefEq lhs rhs then return ← Lean.Meta.mkHEqRefl lhs
      throwError "chart congruence: {lhs} versus {rhs}"
    let ct ← Lean.Meta.mkHCongrWithArity lhs.getAppFn aa.size
    let mut pf := ct.proof
    for i in [:aa.size] do
      let ih ← structuralHEq fuel aa[i]! bb[i]!
      let arg ← match ct.argKinds[i]! with
        | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
        | .heq => pure ih
        | _ => throwError "unexpected chart congruence argument"
      pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
    if (← Lean.Meta.inferType pf).isEq then
      return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]
    return pf

private theorem comp_congr (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z)
    (hr : r = e ≫ p) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p).hom ≫
        (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) hr.symm).hom =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e p r hr := by
  subst r
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, Category.comp_id,
    rightDerivedLowerStarCompHom, conjugateEquiv_leftDerivedUpperStarComp_hom]
  rfl

/-- The chart map uses the canonical composite-adjunction direct-image map.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the composite-adjunction counit in the
identification of each projection with base change of q.
(auxiliary; not a blueprint node).

Proof: write e for the chart, p for its selected projection, and r for the
projective projection, so r=e followed by p. Expand the chart-map definition.
Its four factors are direct image of the chart adjunction unit, the direct-image
composition comparison for e,p, congruence along e followed by p equals r, and
direct image of the shifted line comparison. In the source library,
rightDerivedLowerStarComp_hom_comp_congr_hom identifies the middle two natural
transformations with rightDerivedLowerStarCompHom for r=e followed by p. One can
also prove this identity by substituting that equation: congruence becomes the
identity, and conjugateEquiv_leftDerivedUpperStarComp_hom identifies the remaining
composition comparison with the conjugate of inverse-image composition.
Evaluate this identity at the inverse image of the shifted line. Reassociate the
four factors and compose the identity on the left with the unit and on the right
with the line comparison. Finally replace the particular proof of invertibility
in the definition by hW, using proof irrelevance. This argument uses no exchange,
trace, twist-composition law or positivity of N. It works for both projections,
empty schemes, N=0 and the zero coefficient ring. -/
theorem chartMap_compHom
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool)
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤))) :
    ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
      let e := (projectiveLineDiagonalChart S a).val.hom
      let p := projectiveLineDiagonalProjection S a
      let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
      let B := (ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
      (ordinaryFinitePushforward A p).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app B) ≫
        (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) e p r
          (projectiveLineDiagonalChart S a).property.symm).app
            ((ordinaryFinitePullback A e).obj B) ≫
        (ordinaryFinitePushforward A r).map
          (ordinaryFiniteShiftedLinePullback A N hA t e hW).hom := by
  dsimp only
  unfold ordinaryFiniteP1DiagonalChartMap ordinaryFiniteChartTransport
    ordinaryFiniteAdjunction
  have h := NatTrans.congr_app
    (comp_congr A (projectiveLineDiagonalChart S a).val.hom
      (projectiveLineDiagonalProjection S a)
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
      (projectiveLineDiagonalChart S a).property.symm)
    ((ordinaryFinitePullback A (projectiveLineDiagonalChart S a).val.hom).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧))
  dsimp only [NatTrans.comp_app] at h
  have h' := congrArg (fun k ↦
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (projectiveLineDiagonalChart S a).val.hom).unit.app
            ((ordinaryFiniteLine A N hA
              (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)) ≫
      k ≫ (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (projectiveLineDiagonalChart S a).val.hom hW).hom) h
  simp only [Category.assoc] at h'
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let h := (← Lean.Meta.getLocalDeclFromUserName `h').toExpr
      let heq ← structuralHEq 200 (← Lean.Meta.inferType h) (← g.getType)
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[heq]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h])
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.Etale.SfP1Transport
