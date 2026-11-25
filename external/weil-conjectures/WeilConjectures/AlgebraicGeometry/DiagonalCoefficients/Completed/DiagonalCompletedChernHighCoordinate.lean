/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLocalChernLift
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedModelChernAdjunct
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernExchangeComponents
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalProjectiveModelHyperplanePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # The high coordinate of a normalized completed Chern class -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem unitEndpoint_nonempty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    Nonempty (UnitPullEndpoint Λ f) := by
  refine ⟨⟨(Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).symm, ?_⟩⟩
  exact CondensedRing.homEquiv_εIso_inv_hom Λ f

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor CondensedRing.upperStar CondensedRing.lowerStar
  CompletedRealization.singleUnit CompletedRealization.shiftedLine modelExchange

-- Compare the independently normalized derived functor endpoints.
/-- The geometric exchange has degree one on the normalized Chern component.

Source: diagonal coefficient changes (3), elimination of the base Picard component.
(blueprint: lem-diagonal-completed-chern-high-coordinate).

Proof: lift each local hyperplane Chern class through the fully faithful category
of complete objects. The normalized adjunct comparison identifies their canonical
adjuncts with the two given realized Chern arrows. The local Chern exchange
factorization has a relative term and a term through the base Tate line in degree
minus two. Compose with the given degree-one projection. The base term vanishes
by the standard t-structure, and the relative term is the unit comparison because
the new Chern arrow has degree one. -/
theorem diagonalCompletedChern_highCoordinate (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian X'] [IsNoetherian S']
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (square : IsPullback hX f' f hS)
    (hunit : IsUnit (l : Γ(S, ⊤))) (hunit' : IsUnit (l : Γ(S', ⊤)))
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (eX' : CompletedRealization l X') (eS' : CompletedRealization l S')
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (p' : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f')
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (D' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f'))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (canonical' : D'.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (hcanonical' : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f') D' canonical')
    (push : CompletedPushSquare l f eX eS p.Rc D)
    (push' : CompletedPushSquare l f' eX' eS' p'.Rc D')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS)
    (b : DiagonalTrace.completedUnit l S ⟶
      p.Rc.R.obj ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧))
    (hb : RationalP1.CompletedChernNormalized l p b)
    (b' : DiagonalTrace.completedUnit l S' ⟶
      p'.Rc.R.obj ((DiagonalTrace.completedLine l X')⟦(2 : ℤ)⟧))
    (hb' : RationalP1.CompletedChernNormalized l p' b')
    (τ' : D'.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X') 0).obj
        (zlLine l X'))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S')
    (hBt' : RationalP1.realizeScalarChern l f' eX' eS' p'.Rc D' push' b' ≫ τ' = 𝟙 _) :
    (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS).map
        (RationalP1.realizeScalarChern l f eX eS p.Rc D push b) ≫
      modelExchange _ f f' hX hS square.w.symm D D' canonical canonical' _ ≫
        D'.R.map line.shift ≫ τ' = c.derived := by
  let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
  let V (T : Scheme.{u}) := ((DerivedCategory.singleFunctor (Modules Λ T) 0).obj
    (zlLine l T))⟦(2 : ℤ)⟧
  let F := derivedUpper Λ hS
  let E₀ := modelExchange Λ f f' hX hS square.w.symm D D' canonical canonical' (V X)
  let E := E₀ ≫ D'.R.map line.shift
  let B := RationalP1.realizeScalarChern l f eX eS p.Rc D push b
  let B' := RationalP1.realizeScalarChern l f' eX' eS' p'.Rc D' push' b'
  change F.map B ≫ E₀ ≫ D'.R.map line.shift ≫ τ' = c.derived
  rw [← Category.assoc E₀]
  have hXunit : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hunit.map f.appTop.hom
  have hXunit' : IsUnit (l : Γ(X', ⊤)) := by
    simpa only [map_natCast] using hunit'.map f'.appTop.hom
  obtain ⟨z, hz, _⟩ := DiagonalTrace.diagonalCompletedLocalChern_lift l
    p hXunit (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
      (Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S)))
  obtain ⟨z', hz', _⟩ := DiagonalTrace.diagonalCompletedLocalChern_lift l
    p' hXunit' (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p'.chernX
      (Scheme.Pic.map p'.model.model.hom (SpTowerClasses.hyperplanePic S')))
  have hzN : ModelLocalChernNormalized l p z := by
    unfold ModelLocalChernNormalized
    exact hz
  have hzN' : ModelLocalChernNormalized l p' z' := by
    unfold ModelLocalChernNormalized
    exact hz'
  obtain ⟨cF⟩ := unitEndpoint_nonempty Λ f
  obtain ⟨cF'⟩ := unitEndpoint_nonempty Λ f'
  have hBlocal := diagonalCompletedModelChern_adjunct l f hunit p
    eX eS D canonical hcanonical push cF b hb z hzN
  have hBlocal' := diagonalCompletedModelChern_adjunct l f' hunit' p'
    eX' eS' D' canonical' hcanonical' push' cF' b' hb' z' hzN'
  have hPic := diagonalProjectiveModel_hyperplanePullback f f' hX hS square
    p.model.model p.model.over_eq p'.model.model p'.model.over_eq
  obtain ⟨β, u, hu⟩ := diagonalLocalChern_exchange_components l f f' hX hS square.w.symm
    hunit hunit' p p' eX eX' D canonical hcanonical
    D' canonical' hcanonical' cF cF' line c hPic z z' hzN hzN'
  have : (V S').IsLE (-2) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2) (by decide)
  have hu0 : u ≫ τ' = 0 := DerivedCategory.TStructure.t.zero _ (-2) 0 (by decide)
  have hu' : F.map B ≫ E = β ≫ u + c.derived ≫ B' := by
    dsimp only [B, B', E, E₀]
    rw [hBlocal, hBlocal']
    simpa only [Category.assoc] using hu
  have hBτ' : B' ≫ τ' = 𝟙 _ := hBt'
  have H := congrArg (fun k ↦ k ≫ τ') hu'
  simpa only [E, Preadditive.add_comp, Category.assoc, hu0, hBτ', comp_zero,
    Category.comp_id, zero_add] using H

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
