/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackInterface
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonFormula
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionAugmentationCompatibility
import all WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Augmentation compatibility for the completed reduction tower

The exact-square factor identity and normalized unit equations imply compatibility
of the derived comparison with augmentation, first on resolving complexes and then
on the derived category. These proved helpers support the stratum restriction proof.

## References

* Stacks Tags 03EL, 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] completedReductionModuleTowerFunctor_additive
attribute [local irreducible] HasDerivedCategory.standard
  cochainRepresentativeWhiskering complexCounitNat
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
  completedReductionTower CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors CategoryTheory.Functor.mapDerivedCategoryFactorsh
  CategoryTheory.Functor.mapDerivedCategoryNatIso
attribute [local irreducible] completedReductionModuleTowerFunctor
  completedReductionTowerComplexCounit reductionComplexCounit coherenceReductionTowerCounit

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [local semireducible] completedReductionCoefficient coherenceReductionTowerCounit

private theorem stratumUnit_formula (T : Scheme.{u})
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    letI := completedReductionModuleTowerFunctor_additive T d
    (completedReductionAugmentation d T).app (DerivedCategory.Q.obj P) ≫
        completedReductionTowerComplexCounit T d P =
      (d.constantTower T).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app P) := by
  let _ := completedReductionModuleTowerFunctor_additive T d
  unfold completedReductionTowerComplexCounit reductionComplexCounit
  exact (completedReductionTowerUnit_exists d T).exists.choose_spec P hP

/-- A normalized strict reduction comparison preserves the actual quotient augmentation. -/
theorem completedReduction_augmentationOfComparison {X Y : Scheme.{u}} (f : Y ⟶ X)
    (e : completedReductionModuleTowerFunctor X d ⋙ d.towerModulePull f ≅
      proEtaleRingModulePullback f (d.completedRing X) (d.completedRing Y)
        (d.integralRingIso f) ⋙ completedReductionModuleTowerFunctor Y d)
    (τ : completedReductionTower X d ⋙ d.towerPull f ≅ d.pull f ⋙
      completedReductionTower Y d)
    (hOrd : ∀ M : reductionModules X (d.completedRing X),
      (d.towerModulePull f).map ((completedReductionModuleUnit d X).app M) ≫ e.hom.app M =
        (d.constantPullbackIso f).hom.app M ≫ (completedReductionModuleUnit d Y).app
          ((proEtaleRingModulePullback f (d.completedRing X) (d.completedRing Y)
            (d.integralRingIso f)).obj M))
    (hnorm : ∀ P : CochainComplex (reductionModules X (d.completedRing X)) ℤ,
      P.IsKFlatIndependentCoefficients →
      DerivedReductionComparisonFormula
        (proEtaleRingModulePullback f (d.completedRing X) (d.completedRing Y)
          (d.integralRingIso f)) (d.towerModulePull f)
        (completedReductionModuleTowerFunctor X d) (completedReductionModuleTowerFunctor Y d)
        (completedReductionTower X d) (completedReductionTower Y d)
        (completedReductionTowerComplexCounit X d) (completedReductionTowerComplexCounit Y d)
        e τ P)
    (hflat : ∀ P : CochainComplex (reductionModules X (d.completedRing X)) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := d.completedRing X) (P.X n)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing Y)
        (((proEtaleRingModulePullback f (d.completedRing X) (d.completedRing Y)
          (d.integralRingIso f)).mapHomologicalComplex (.up ℤ)).obj P))
    (K : d.derived X) :
    (d.towerPull f).map ((completedReductionAugmentation d X).app K) ≫ τ.hom.app K =
      (d.derivedConstantPullbackIso f).hom.app K ≫
        (completedReductionAugmentation d Y).app ((d.pull f).obj K) := by
  let F := proEtaleRingModulePullback f (d.completedRing X) (d.completedRing Y)
    (d.integralRingIso f)
  let good : ObjectProperty (CochainComplex (reductionModules X (d.completedRing X)) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := d.completedRing X) (P.X n)
  have res (L : CochainComplex (reductionModules X (d.completedRing X)) ℤ) :
      ∃ P, ∃ p : P ⟶ L, good P ∧ QuasiIso p := by
    obtain ⟨P, p, hP, hflat, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := d.completedRing X) L
    exact ⟨P, p, ⟨hP, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (d.completedRing X) (P.X n)).symm
        (hflat n)⟩, hp⟩
  exact derivedReduction_augmentationOfCounits
    F (d.towerModulePull f)
    (completedReductionModuleTowerFunctor X d) (d.constantTower X)
    (completedReductionModuleTowerFunctor Y d) (d.constantTower Y)
    (completedReductionTower X d) (completedReductionTower Y d)
    (completedReductionTowerComplexCounit X d) (completedReductionTowerComplexCounit Y d)
    (completedReductionModuleUnit d X) (completedReductionModuleUnit d Y)
    (completedReductionAugmentation d X) (completedReductionAugmentation d Y)
    e (d.constantPullbackIso f) τ
    good res
    (fun P hP ↦ towerCounit_isIso Y d _ (hflat P hP.1 hP.2))
    (fun P hP ↦ hnorm P hP.1)
    (fun P hP ↦ stratumUnit_formula d X P hP.1)
    (fun P hP ↦ stratumUnit_formula d Y _ (hflat P hP.1 hP.2))
    hOrd K

end AlgebraicGeometry.Scheme
