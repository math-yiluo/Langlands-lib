/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorLocalization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricCoefficientTower
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Existence of the geometric operation data

Source: Zheng Construction 4.1 and Lemma 4.10.
(blueprint: lem-coef-semilinear-geometric-operations-base-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace CategoryTheory.Adjunction

private theorem canonical_transpose
    {X Y : Type*} [Category X] [Category Y] [Abelian X] [Abelian Y]
    [HasDerivedCategory X] [HasDerivedCategory Y] [Abelian.HasKInjectiveResolutions Y]
    {L : X ⥤ Y} {R : Y ⥤ X} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ R)
    (P : CochainComplex X ℤ) (I : CochainComplex Y ℤ) [I.IsKInjective]
    (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ I) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (L.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
        (R.rightDerivedFunctorObjQIso I).inv := by
  let ah := a.mapHomotopyCategory (.up ℤ)
  let ad := a.mapDerivedCategoryRightDerivedAdjunction
  let π := HomotopyCategory.quotient X (.up ℤ)
  have hu := ah.derivedη_fac_app (HomotopyCategory.quasiIso X (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit (π.obj P)
  change ad.unit.app _ ≫ R.rightDerivedFunctor.map
    (L.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) = _
  rw [R.rightDerivedFunctor.map_comp, ← Category.assoc]
  have hu' : ad.unit.app (DerivedCategory.Q.obj P) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      R.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
    have hα : L.mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso X).hom.app P) ≫
          L.mapDerivedCategoryFactors.hom.app P =
        L.mapDerivedCategoryFactorsh.hom.app (π.obj P) ≫
          (DerivedCategory.quotientCompQhIso Y).hom.app
            ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
      rw [L.mapDerivedCategoryFactorsh_hom_app]
      simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    have hu₀ : ad.unit.app (DerivedCategory.Qh.obj (π.obj P)) ≫
          R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app (π.obj P)) =
        DerivedCategory.Qh.map (π.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P)) ≫
          R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient Y (.up ℤ)).obj
            ((L.mapHomologicalComplex (.up ℤ)).obj P)) := by
      dsimp only [ah, π] at hu
      rw [a.mapHomotopyCategory_unit_app_quotient (c := .up ℤ) P] at hu
      exact hu
    have hn := ad.unit.naturality ((DerivedCategory.quotientCompQhIso X).hom.app P)
    change (DerivedCategory.quotientCompQhIso X).hom.app P ≫
        ad.unit.app (DerivedCategory.Q.obj P) =
      ad.unit.app (DerivedCategory.Qh.obj (π.obj P)) ≫
        R.rightDerivedFunctor.map
          (L.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso X).hom.app P)) at hn
    apply (cancel_epi ((DerivedCategory.quotientCompQhIso X).hom.app P)).mp
    calc
      _ = (ad.unit.app (DerivedCategory.Qh.obj (π.obj P)) ≫
            R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app (π.obj P))) ≫
          R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso Y).hom.app
            ((L.mapHomologicalComplex (.up ℤ)).obj P)) := by
        rw [← Category.assoc, hn, Category.assoc, ← R.rightDerivedFunctor.map_comp,
          hα, R.rightDerivedFunctor.map_comp, ← Category.assoc]
      _ = DerivedCategory.Qh.map (π.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P)) ≫
          R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient Y (.up ℤ)).obj
            ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso Y).hom.app
            ((L.mapHomologicalComplex (.up ℤ)).obj P)) := by rw [hu₀, Category.assoc]
      _ = _ := by
        symm
        dsimp only [Functor.rightDerivedFunctorUnitQ]
        rw [← Category.assoc, ← DerivedCategory.quotientCompQhIso_hom_naturality]
        dsimp only [Functor.comp_obj]
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
        rfl
  rw [hu', Category.assoc, ← R.rightDerivedFunctorUnitQ_naturality f,
    ← DerivedCategory.Q.map_comp_assoc, R.rightDerivedFunctorUnitQ_eq I]
  rfl

end CategoryTheory.Adjunction

namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The termwise inverse/direct image construction supplies the geometric-operation data.
The construction uses the induced coefficient tower, ordinary module adjunctions, and their
canonical derived localizations; the normalized tensor and evaluation comparisons are part of
the same construction. -/
theorem semilinearGeometryBaseExistence (systems : Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    Nonempty (Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet) := by
  classical
  obtain ⟨F, σ, I, hI⟩ := geometricCoefficientTower.{c, v, r} J B τ J' uInv
  obtain ⟨⟨O, _⟩⟩ :=
    semilinearGeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet F σ I hI
  obtain ⟨S⟩ := semilinearSystemData.{c, v, r} J' O.coefficients O.coefficientTransition
  let target := S.systems
  let : ∀ n : ℕ, IsGrothendieckAbelian.{max c v r}
      (Mod.{c, v, max c v r} J' (O.coefficients n)) :=
    fun n ↦
      (@grothendieckAbelian_and_functorial_kInjective_resolutionsMixedUniverses.{c, v, max c v r}
        C' _ J' (abelianSheafify.{c, v, max c v r} J')
        (locallyBijective.{c, v, max c v r} J')
        (CategoryTheory.hasSheafCompose_commRingToRing J') (O.coefficients n)).1
  let : ∀ n : ℕ, Abelian.HasKInjectiveResolutions
      (Mod.{c, v, max c v r} J' (O.coefficients n)) := fun n ↦
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max c v r}
      (C := Mod.{c, v, max c v r} J' (O.coefficients n))
  let : IsGrothendieckAbelian.{max c v r}
      (Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition) := target.grothendieck
  let : Abelian.HasKInjectiveResolutions
      (Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max c v r}
  obtain ⟨E⟩ := semilinearGeometryEvaluation.{c, v, r} J B τ J' uInv uPush adjSet systems O target
  obtain ⟨T⟩ := semilinearGeometryTensor.{c, v, r} J B τ J' uInv uPush adjSet systems O target
  refine ⟨{
    toGeometryBase := GeometryOrdinary.toBase.{c, v, r} J B τ J' uInv uPush adjSet O target
    derivedLevelAdjunction := fun n ↦
      (O.levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
    derivedLevelAdjunction_canonical := fun _ ↦ rfl
    derivedAdjunction_canonical := rfl
    pullEvaluation := geometryPullEvaluation.{c, v, r} J B τ J' uInv uPush adjSet O
    pushEvaluation := E.pushEvaluation
    unit_evaluation := E.unit_evaluation
    counit_evaluation := E.counit_evaluation
    coefficientPullback := E.coefficientPullback
    tensorPullback := T.tensorPullback
    levelTensorPullback := T.levelTensorPullback
    tensorPullback_evaluation := T.tensorPullback_evaluation
    ordinaryPullEvaluation_sections := by
      dsimp only [GeometryOrdinary.toBase]
      exact O.ordinaryPullEvaluation_sections
    ordinaryPushEvaluation := O.ordinaryPushEvaluation
    ordinaryPushEvaluation_sections := O.ordinaryPushEvaluation_sections
    ordinary_unit_evaluation := O.ordinary_unit_evaluation
    derivedLevel_transpose_model := ?_
    derived_transpose_model := ?_
    pullEvaluation_model := fun _ ↦ rfl
    restrictionPullback := O.restrictionPullback
    restrictionPullback_underlying := O.restrictionPullback_underlying
    ordinaryPullTransition := by
      dsimp only [GeometryOrdinary.toBase]
      exact O.ordinaryPullTransition
    coefficientPullback_transpose := E.coefficientPullback_transpose
    levelTensorModel := T.levelTensorModel
    levelTensor_pure := T.levelTensor_pure
    tensorModel := T.tensorModel
    tensor_ordinary_evaluation := by
      dsimp only [GeometryOrdinary.toBase]
      exact T.tensor_ordinary_evaluation }⟩
  · intro n P I _ f
    exact CategoryTheory.Adjunction.canonical_transpose (O.levelAdjunction n) P I f
  · intro P I _ f
    exact CategoryTheory.Adjunction.canonical_transpose O.ordinaryAdjunction P I f

end WeilConjectures.SemilinearSections
