/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit

/-! # Forgetting supports in the diagonal section map

This normalization involves only one self-product, with no change of coordinates.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the diagonal section
identification (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  upperStar lowerStar ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteUnitPullback rightDerivedLowerShriek
  rightDerivedLowerShriekIsoRightDerivedLowerStar derivedTensorUnit

-- Compare recorded instances without expanding the derived localization constructions.
-- This kernel-checked congruence method follows OrdinaryFiniteDiagonalChartExchangeAux.
private meta def unfoldBoundary (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if let .fvar id := e then
    if let some v := (← id.getDecl).value? then return some v
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  let names : List Lean.Name := [``DerivedCategoryModule, ``ordinaryFinitePushforward,
    ``ordinaryFinitePullback, ``ordinaryFiniteUnit,
    ``ordinaryFiniteDerivedCategoryInstance, ``ordinaryFiniteSingleFunctor]
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
  | 0, _, _ => throwError "coefficient congruence exhausted its structural depth"
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
      throwError "coefficient congruence: {lhs} versus {rhs}"
    let ct ← Lean.Meta.mkHCongrWithArity lhs.getAppFn aa.size
    let mut pf := ct.proof
    for i in [:aa.size] do
      let ih ← structuralHEq fuel aa[i]! bb[i]!
      let arg ← match ct.argKinds[i]! with
        | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
        | .heq => pure ih
        | _ => throwError "unexpected coefficient congruence argument"
      pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
    if (← Lean.Meta.inferType pf).isEq then
      return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]
    return pf

private theorem coefficient_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F R : D ⥤ E) (Q : C ⥤ D) (α : F ⟶ R)
    {U U₁ U₂ : E} {V W K : C} {Y : D}
    (s : U ⟶ F.obj Y) (j : Y ⟶ Q.obj W)
    (t₁ : U ⟶ U₁) (t₂ : U₁ ⟶ U₂) (t₃ : U₂ ⟶ R.obj (Q.obj V))
    (c : V ⟶ W)
    (h : s ≫ F.map (j ≫ Q.map (𝟙 W)) ≫ α.app (Q.obj W) =
      t₁ ≫ t₂ ≫ t₃ ≫ R.map (Q.map (c ≫ 𝟙 W))) (θ : W ⟶ K) :
    s ≫ F.map (j ≫ Q.map θ) ≫ α.app (Q.obj K) =
      t₁ ≫ t₂ ≫ t₃ ≫ R.map (Q.map (c ≫ θ)) := by
  rw [Q.map_id] at h
  simp only [Category.comp_id] at h
  have hpost := congrArg (fun q ↦ q ≫ R.map (Q.map θ)) h
  simp only [F.map_comp, R.map_comp, Q.map_comp, Category.assoc] at hpost ⊢
  rw [α.naturality (Q.map θ)]
  exact hpost

/-- Forget-supports identifies the compact-support diagonal section map with the
composite of the two ordinary constant-object units, naturally in a map from
the tensor unit to any coefficient object on the original scheme.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the identification
M = Rp2_* Delta_* M, and lem-amb-p1-diagonal-integrals.proof.md, the diagonal
is a section for either projection.
(auxiliary; not a blueprint node).

Proof: put d = Delta and p = p_a, so d followed by p is identity.
Expand rightDerivedLowerShriekCompIso in its specified compatible tower:
use the chosen compactification of p and the compactification of d followed
by its open immersion obtained from the chosen compactification of d p.
In this tower the compositor is proper/open exchange followed by composition
of open extensions and composition of proper direct images. Substitute the
adjunction-mate formula for exchange. Naturality of the maps from open
extension to ordinary direct image, followed by the mate counit identity,
identifies the two forget-supports maps with the ordinary compositor.
The theorem rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar
in CompactificationRefinementLowerStar transports the tower calculation to
the chosen models for d and d p. Equivalently this is the calculation with
identity compactifications, where open extension is identity.
The identity comparison is, by definition,
forget-supports followed by the ordinary direct-image identity comparison.
Consequently the inverse identity/composition map used in diagonalUnit,
followed by the two forget-supports maps, is the inverse ordinary section
compositor. Under the constant-to-tensor-unit comparison, the ordinary section
compositor is the composite of the constant-object units for p and d: the
composition mate identity identifies it with the constant-object unit for
identity, which is identity because the constant-sheaf pullback comparisons
respect identity and composition. Naturality of proper forget-supports moves
the constant-to-tensor-unit comparison to the source. Postcompose this
normalization with Rp_* Rd_* of the map c.hom followed by theta, where
c is the constant-to-tensor-unit comparison. Naturality moves this map into
the diagonal direct image. The composite c.inv followed by c.hom is identity,
so functoriality leaves precisely theta inside the diagonal direct image on
the left. This gives the displayed formula for every coefficient object and
map theta, keeping that map intact.
The two Boolean cases use respectively diagonal_fst and diagonal_snd; no
projective-line isomorphism or base-change map is involved. The argument
applies unchanged to empty schemes and the zero coefficient ring. -/
theorem diagonalSection_forgetSupports
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (a : Bool)
    (K : DerivedCategoryModule A X)
    (θ : derivedTensorUnit (ModuleCat.{u + 1} A) X ⟶ K) :
    diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).map
          ((ordinaryProperForgetComparison A
              (TraceDiagonalDatum.diagonal f)).hom.app
                (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
            (ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map θ) ≫
        (ordinaryProperForgetComparison A
          (projection f a)).hom.app
            ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).obj K) =
      (constantUnit A X).inv ≫ supportedDerivedUnit A (projection f a) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          (supportedDerivedUnit A (TraceDiagonalDatum.diagonal f)) ≫
        (ordinaryFinitePushforward A (projection f a)).map
        ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
            ((constantUnit A X).hom ≫ θ)) := by
  have hunit := diagonalSection_forgetSupports_unit A f a
  have hnormalized := coefficient_naturality
    (C := DerivedCategoryModule A X)
    (D := DerivedCategoryModule A (pullback f f))
    (E := DerivedCategoryModule A X)
    (U := derivedTensorUnit (ModuleCat.{u + 1} A) X)
    (U₁ := ordinaryFiniteUnit A X)
    (U₂ := (ordinaryFinitePushforward A (projection f a)).obj
      (ordinaryFiniteUnit A (pullback f f)))
    (V := ordinaryFiniteUnit A X)
    (W := derivedTensorUnit (ModuleCat.{u + 1} A) X) (K := K)
    (Y := (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (TraceDiagonalDatum.diagonal f)).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a))
    (ordinaryFinitePushforward A (projection f a))
    (ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f))
    (ordinaryProperForgetComparison A (projection f a)).hom
    (diagonalUnit A f a)
    ((ordinaryProperForgetComparison A (TraceDiagonalDatum.diagonal f)).hom.app
      (derivedTensorUnit (ModuleCat.{u + 1} A) X))
    (constantUnit A X).inv (supportedDerivedUnit A (projection f a))
    ((ordinaryFinitePushforward A (projection f a)).map
      (supportedDerivedUnit A (TraceDiagonalDatum.diagonal f)))
    (constantUnit A X).hom (by
      run_tac
        let g ← Lean.Elab.Tactic.getMainGoal
        g.withContext do
          let some decl := (← Lean.getLCtx).findFromUserName? `hunit
            | throwError "unit normalization is missing"
          let h := decl.toExpr
          let e ← structuralHEq 200 (← Lean.Meta.inferType h) (← g.getType)
          let e ← Lean.Meta.mkAppM ``eq_of_heq #[e]
          g.assign (← Lean.Meta.mkAppM ``Eq.mp #[e, h])
        Lean.Elab.Tactic.replaceMainGoal []) θ
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let some decl := (← Lean.getLCtx).findFromUserName? `hnormalized
        | throwError "coefficient normalization is missing"
      let h := decl.toExpr
      let e ← structuralHEq 200 (← Lean.Meta.inferType h) (← g.getType)
      let e ← Lean.Meta.mkAppM ``eq_of_heq #[e]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[e, h])
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.Etale.SfP1Transport
