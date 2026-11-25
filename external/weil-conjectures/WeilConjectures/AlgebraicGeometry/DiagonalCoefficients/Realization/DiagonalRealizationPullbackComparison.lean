/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackCanonicalComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackUnitComponent
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackLineComponent

/-! # Endpoint components of the derived completed realization comparison
(blueprint: lem-sfb-diagonal-realization-pullback-derived). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem commShift_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} (s t : F.CommShift ℤ)
    (h : ∀ n, F.commShiftIso (self := s) n = F.commShiftIso (self := t) n) : s = t := by
  cases s
  cases t
  congr 1
  funext n
  exact h n

private theorem adjoint_shift_eq
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [s : F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] :
    adj.leftAdjointCommShift ℤ = s := by
  apply commShift_ext
  intro n
  exact Adjunction.CommShift.compatibilityUnit_unique_left adj _ _ _
    (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj n)
    (adj.shift_unit_app n)

private theorem geometric_shift
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.CommShift (F₁ := derivedUpper R f)
      (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom ℤ := by
  have ha := (CondensedRing.kflat_derived_adjunction_transport_shifts
    (Mon.mk R) f).2.2
  letI : (CondensedRing.derivedUpperStarLowerStarAdjunction R f).CommShift ℤ := ha
  have he : derivedUpperCommShift R f =
      CondensedRing.modulePullbackDerivedCommShift R f := by
    exact adjoint_shift_eq
      (F := CondensedRing.moduleObjectDerivedPullback R f)
      (G := CondensedRing.moduleObjectDerivedPushforward R f)
      (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
  change NatTrans.CommShift (F₁ := derivedUpper R f)
    (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
    (CondensedRing.modulePullbackExactComparison R f).hom ℤ
  rw [he]
  exact (CondensedRing.module_derived_functors_exact_and_comparison_shifts R f).2.2.1

structure DiagonalRealizationPullbackComparisonData (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f coeff) where
  comparison : (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategory ⋙ eX.F.mapDerivedCategory ≅
    eS.F.mapDerivedCategory ⋙ derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  shifts : NatTrans.CommShift comparison.hom ℤ
  unit_component : comparison.hom.app (DiagonalTrace.completedUnit l S) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.singleUnit l S) ≫ unit.derived =
    eX.F.mapDerivedCategory.map
      ((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategorySingleFunctor 0 |>.app
          (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)))
        |>.trans ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
          d.completedUnit)).hom ≫
      eX.singleUnit l X
  line_component : comparison.hom.app ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.shiftedLine l S) ≫ line.shift =
    eX.F.mapDerivedCategory.map
      (((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategory.commShiftIso (2 : ℤ)).app _
      ≪≫ (shiftFunctor (DerivedCategory (DiagonalCompleted l X)) (2 : ℤ)).mapIso
        ((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategorySingleFunctor 0 |>.app
            (Scheme.purTwistZlModule S l) |>.trans
              ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
                d.completedLine))).hom ≫
      eX.shiftedLine l X

/-- The derived pullback comparison has the prescribed unit and shifted line components.
Source: diagonal coefficient changes paragraph (3), proof steps 2, 3 and 6.
(blueprint: lem-sfb-diagonal-realization-pullback-derived).

Proof: first identify diagonalTracePush with the right adjoint of the completed
pullback. Both are sheaf direct image with scalar action through the adjoint
coefficient map; the tensor/direct-image Hom formula identifies their specified
adjunctions. Transfer the normalized ordinary direct-image square along this
identification and form its inverse mate across the two exact realization
equivalences. The full adjunction Hom
equation fixes the inverse-image comparison. Forgetting this equation and using
the underlying normalization identifies its abelian transpose with the inverse
image of the realization comparison. The endpoint adjoint normalizations then
identify the ordinary unit and root components. Localize this ordinary natural
isomorphism term by term. Exact derivation preserves inverses and naturality;
the exact single-functor formula gives the unit component, and its shifted
version gives the line component. These localized transformations commute with
the canonical integer shifts. -/
theorem diagonalRealization_pullback_comparison (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian X] [IsNoetherian S]
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    (hc : coeff.hom = diagonalCompletedCoefficientMap l f)
    (hX : IsUnit (l : Γ(X, ⊤))) (hS : IsUnit (l : Γ(S, ⊤)))
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f coeff) :
    Nonempty (DiagonalRealizationPullbackComparisonData l f coeff eX eS unit line d) := by
  have hmap : IsIso (diagonalCompletedCoefficientMap l f) := by
    rw [← hc]
    infer_instance
  let ciso := @asIso _ _ _ _ (diagonalCompletedCoefficientMap l f) hmap
  have hcoeff : coeff = ciso := by
    apply Iso.ext
    exact hc
  subst coeff
  letI : eS.F.asEquivalence.functor.Additive := inferInstanceAs eS.F.Additive
  letI : eX.F.asEquivalence.functor.Additive := inferInstanceAs eX.F.Additive
  let raw := Functor.mapDerivedCategorySquareIso
    (diagonalPullbackOrdinaryComparison l f eX eS)
  let upperIso := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  let comparison := diagonalRealization_pullback_canonical_comparison l f eX eS ciso hc
  refine ⟨{
    comparison := comparison
    shifts := by
      letI : (CondensedRing.upperStar
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).leftDerivedFunctor.CommShift ℤ :=
        derivedUpperCommShift (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      have hg : NatTrans.CommShift
          (F₁ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
          (F₂ := (CondensedRing.upperStar
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
          upperIso.hom ℤ :=
        geometric_shift (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      have hu : NatTrans.CommShift
          (F₁ := (CondensedRing.upperStar
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
          (F₂ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
          upperIso.symm.hom ℤ := by
        letI : NatTrans.CommShift
            (F₁ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
            (F₂ := (CondensedRing.upperStar
              (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
            upperIso.hom ℤ := hg
        infer_instance
      have hr : NatTrans.CommShift raw.hom ℤ := by
        dsimp [raw]
        infer_instance
      letI : NatTrans.CommShift
          (F₁ := (CondensedRing.upperStar
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
          (F₂ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
          upperIso.symm.hom ℤ := hu
      have hc : NatTrans.CommShift
          (F₁ := (Scheme.proEtaleRingModulePullback f
            (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
            ciso).mapDerivedCategory ⋙ eX.F.mapDerivedCategory)
          (F₂ := eS.F.mapDerivedCategory ⋙
            derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
          (raw.hom ≫ Functor.whiskerLeft eS.F.mapDerivedCategory upperIso.symm.hom) ℤ := by
        exact NatTrans.CommShift.comp (τ := raw.hom)
          (τ' := Functor.whiskerLeft eS.F.mapDerivedCategory upperIso.symm.hom) ℤ
      have hn : comparison = diagonalPullbackDerivedComparison l f eX eS := by
        exact diagonalRealization_pullback_canonical_comparison_normalized l f eX eS _
      rw [hn]
      simpa only [diagonalPullbackDerivedComparison, raw,
        derivedUpper, upperIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom] using hc
    unit_component := by
      exact diagonalRealization_pullback_unit_component l f ciso hc hX hS eX eS unit line d
    line_component := by
      exact diagonalRealization_pullback_line_component l f ciso hc hX hS eX eS unit line d
  }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
