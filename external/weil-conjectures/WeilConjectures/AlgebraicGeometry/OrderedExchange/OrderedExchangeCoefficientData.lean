/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeRhoLambda
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeRhoLambda
public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionTower
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.CategoryTheory.FlatScalarTowerLimit.FlatScalarTowerLimitSquare
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitDerived
import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionAugmentationCompatibility

/-! # Coefficient normalization of the raw ordered completed exchange

The maps below retain their ordinary-section, universal-derived-counit and completion-unit
normalizations. The ambient constant and completed module categories remain distinct.

## References

* Stacks Tags 099M, 0941 and 0A07
* Stacks 0D6D
* Stacks Tags 099C, 099I and 099M
* Stacks 099N
* Stacks 099M, 0E48
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

-- Prefer the concrete pro-etale site and module instances to abstract corner projections.
attribute [local instance 0] SheafOfModules.RingedTensorCorner.category
  SheafOfModules.RingedTensorCorner.derived

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  completedAdicChange reductionChange reductionDerivedChange reductionHomotopy
  completedReductionTower reduction

attribute [local instance 3000] orderedAbSheafify orderedAbLocallyBijective
  reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
  reductionRingModulesHasDerivedCategory

-- Normalize the two ordinary presentations of scalar restriction before matching complexes.
set_option allowUnsafeReducibility true in
attribute [local reducible] reductionRestrict completedReductionComplexTowerFunctor

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [local irreducible] ordinaryRho reductionModule completedReductionModuleTowerFunctor
  completedReductionCoefficient constantSheaf AdicCoefficients.coefficientRing
  SheafOfModules.monoidalCategory

attribute [local irreducible] RhoNormalization
attribute [local irreducible] ordinaryLambda Functor.rightDerivedFunctor
attribute [local irreducible] limitComplexUnit
attribute [local irreducible] LambdaNormalization
attribute [local irreducible] SheafOfModules.fullyFaithfulForget

section RhoUnitFirst

attribute [local semireducible] completedReductionCoefficient constantSheaf
  AdicCoefficients.coefficientRing

/-- The derived quotient augmentation on a complex, through the reduction counit. -/
theorem augmentation_complexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (augmentation d T).app (DerivedCategory.Q.obj P) ≫ reductionComplexCounit d T P =
      (Functor.const ℕᵒᵖ).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinaryAugmentation d T) (.up ℤ)).app P) := by
  let := (reductionData d T).isLeftDerived
  unfold augmentation
  with_unfolding_all exact (lift_complex_fac (Functor.const ℕᵒᵖ) (reductionModule d T)
    (reductionData d T).reduction (reductionData d T).counit (ordinaryAugmentation d T)
    (canonicalModelAugmentation (Functor.const ℕᵒᵖ) (reductionModule d T)
      (reductionData d T) (ordinaryAugmentation d T))
    (fun K ↦ (reductionData d T).reduction.leftDerived_fac_app (reductionData d T).counit
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ K) P)

/-- The ordinary balancing comparison preserves the quotient augmentations. -/
theorem ordinaryRho_augmentation (T : Scheme.{t}) (M : reductionModules T (d.completedRing T)) :
    (exchangeTowerModuleRes d T).map ((completedReductionModuleUnit d T).app M) ≫
        (ordinaryRho d T).symm.hom.app M =
      (ordinaryScalarDiagonal d T).hom.app M ≫
        (ordinaryAugmentation d T).app ((reductionRestrict T (exchangeScalar d T)).obj M) := by
  have hρ := (ordinaryRho_existsUnique d T).exists.choose_spec
  rw [Iso.symm_hom, ← Iso.app_inv, Iso.comp_inv_eq, Iso.app_hom]
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hu := (completedReductionModuleUnit_exists d T).exists.choose_spec M n U x
  have ha := (ordinaryAugmentation_existsUnique d T).exists.choose_spec
    ((reductionRestrict T (exchangeScalar d T)).obj M) n U x
  change ((((completedReductionModuleUnit d T).app M).app (op n)).val.app U x) =
    (((ordinaryRho d T).hom.app M).app (op n)).val.app U
      ((((ordinaryAugmentation d T).app
        ((reductionRestrict T (exchangeScalar d T)).obj M)).app (op n)).val.app U x)
  unfold ordinaryAugmentation ordinaryRho completedReductionModuleUnit
  rw [ha, hρ, hu]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The completed quotient augmentation on a K-flat complex, through the tower counit. -/
theorem completedReductionAugmentation_complexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing T) P) :
    (completedReductionAugmentation d T).app (DerivedCategory.Q.obj P) ≫
        completedReductionTowerComplexCounit T d P =
      (d.constantTower T).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (F := d.constantTower T)
            (G := completedReductionModuleTowerFunctor T d) (completedReductionModuleUnit d T)
            (.up ℤ)).app P) := by
  have h := (completedReductionTowerUnit_exists d T).exists.choose_spec P hP
  dsimp only [HasCompletedReductionTowerUnitNormalization, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
    Functor.mapHomotopyCategoryFactors, NatIso.ofComponents, Iso.refl] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  unfold completedReductionTowerComplexCounit Scheme.reductionComplexCounit
  change _ ≫ ((completedReductionTower T d).map (𝟙 _) ≫
    (coherenceReductionTowerCounit T d).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _) = _
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.comp_id]
  exact h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction respects the strict quotient unit, not just its evaluations. -/
theorem rho_unit_first (T : Scheme.{t}) (K : d.derived T) :
    (exchangeTowerRes d T).map ((completedReductionAugmentation d T).app K) ≫
        (rho d T).hom.app K =
      (scalarDiagonal d T).hom.app K ≫ (augmentation d T).app ((res d T).obj K) := by
  have hflat := orderedScalarFlat d T
  let c := exchangeScalar d T
  let good : ObjectProperty (CochainComplex (reductionModules T (d.completedRing T)) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
        (R := d.completedRing T) (P.X n)
  have hkflat (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) (hP : good P) :=
    (SheafOfModules.isKFlat_restrictScalars_of_flat c hflat P hP.1).1
  have hiso (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) (hP : good P) :
      IsIso (reductionComplexCounit d T
        (((reductionRestrict T c).mapHomologicalComplex (.up ℤ)).obj P)) := by
    have hi := (reductionData d T).complexCounit_isIso _ (hkflat P hP)
    simpa only [reductionComplexCounit, reduction] using hi
  have hnorm : RhoNormalization d T (rho d T) := (rho_existsUnique d T).exists.choose_spec
  unfold RhoNormalization at hnorm
  exact derivedReduction_augmentationOfCounits (reductionRestrict T c)
    (exchangeTowerModuleRes d T)
    (completedReductionModuleTowerFunctor T d) (d.constantTower T)
    (reductionModule d T) (Functor.const ℕᵒᵖ)
    (completedReductionTower T d) (reduction d T)
    (completedReductionTowerComplexCounit T d) (reductionComplexCounit d T)
    (completedReductionModuleUnit d T) (ordinaryAugmentation d T)
    (completedReductionAugmentation d T) (augmentation d T)
    (ordinaryRho d T).symm (ordinaryScalarDiagonal d T) (rho d T)
    good (flatKFlatResolution T (d.completedRing T)) hiso
    (fun P hP ↦ by
      unfold DerivedReductionComparisonFormula
      exact hnorm P hP.1 hP.2)
    (fun P hP ↦ completedReductionAugmentation_complexCounit d T P hP.1)
    (fun P _ ↦ augmentation_complexCounit d T _)
    (ordinaryRho_augmentation d T) K

end RhoUnitFirst

/-- The normalized strict-tower comparison preserves the actual completion units. -/
theorem rho_unit_second (T : Scheme.{t}) (K : d.derived T) :
    (res d T).map (d.completionUnit T K) ≫
        (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) =
      (unit d T).app ((res d T).obj K) := by
  have hn := (lambda d T).hom.naturality ((completedReductionAugmentation d T).app K)
  have h1 := rho_unit_first d T K
  have h2 := lambda_unit d T K
  simp only [Functor.comp_map] at hn
  have key : (res d T).map ((d.constantRlimAdjunction T).unit.app K) ≫
      (res d T).map ((completedRlim T (d.completedRing T)).map
        ((completedReductionAugmentation d T).app K)) ≫
      (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
      (rlim (A := A) T).map ((rho d T).hom.app K) =
      (diagonalAdjunction (A := A) T).unit.app ((res d T).obj K) ≫
        (rlim (A := A) T).map ((augmentation d T).app ((res d T).obj K)) := by
    rw [reassoc_of% hn, ← Functor.map_comp, h1, Functor.map_comp, ← h2]
    simp only [Category.assoc]
  unfold AdicCoefficientDatum.completionUnit
  erw [Functor.map_comp, Category.assoc]
  exact key

theorem rho_unit (T : Scheme.{t}) (K : d.derived T) :
    (exchangeTowerRes d T).map ((completedReductionAugmentation d T).app K) ≫
        (rho d T).hom.app K =
      (scalarDiagonal d T).hom.app K ≫ (augmentation d T).app ((res d T).obj K) ∧
    (res d T).map (d.completionUnit T K) ≫
        (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) =
      (unit d T).app ((res d T).obj K) := by
  exact ⟨rho_unit_first d T K, rho_unit_second d T K⟩

variable {U V : Scheme.{t}} (u : U ⟶ V)

/-- The ambient direct-image/scalar comparison, with its universal unit normalization. -/
def chi : d.push u ⋙ res d V ≅ res d U ⋙ push (A := A) u :=
  proEtaleRingRestrictionDerivedDirectImage u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The ambient pullback/scalar comparison is exact descent of the ordinary normalized mate. -/
def alpha : d.pull u ⋙ res d U ≅ res d V ⋙ pull (A := A) u :=
  proEtaleRingRestrictionDerivedPullback u
    (exchangeConstantRing V A) (d.completedRing V)
    (exchangeConstantRing U A) (d.completedRing U)
    (exchangeScalar d V) (exchangeScalar d U) (exchangeConstantIso u A)
    (d.integralRingIso u) (exchangeScalar_comm d u)

/-- The quotient-tower complete category over completed coefficients. -/
abbrev AComplete (T : Scheme.{t}) := ObjectProperty.FullSubcategory (d.TowerComplete T)

/-- The inclusion of the full completed-coefficient complete category. -/
abbrev inclusion (T : Scheme.{t}) := ObjectProperty.ι (d.TowerComplete T)

/-- Restriction identifies the two complete predicates and is an equivalence on the full
complete categories; it does not assert an ambient equivalence. -/
theorem restriction_complete_iff (T : Scheme.{t}) :
    ∀ K : d.derived T, d.TowerComplete T K ↔ IsComplete d T ((res d T).obj K) := by
  have hr : (res d T).ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction (𝟙 T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeScalar d T) (exchangeScalar d T) (exchangeConstantIso (𝟙 T) A)
      (d.integralRingIso (𝟙 T)) (exchangeScalar_comm d (𝟙 T))).1
  intro K
  let q := (lambda d T).app ((completedReductionTower T d).obj K) ≪≫
    (rlim (A := A) T).mapIso ((rho d T).app K)
  have hq : (res d T).map (d.completionUnit T K) ≫ q.hom =
      (unit d T).app ((res d T).obj K) := rho_unit_second d T K
  change IsIso (d.completionUnit T K) ↔ IsIso ((unit d T).app ((res d T).obj K))
  rw [← hq]
  constructor
  · intro h
    have := h
    infer_instance
  · intro h
    have := h
    have : IsIso ((res d T).map (d.completionUnit T K)) :=
      IsIso.of_isIso_comp_right _ q.hom
    exact isIso_of_reflects_iso (d.completionUnit T K) (res d T)

/-- The completed quotient completion followed by restriction is the constant quotient
completion of the restriction, through the specified comparisons lambda and rho. -/
def completedComparison (T : Scheme.{t}) :
    (completedReductionTower T d ⋙ completedRlim T (d.completedRing T)) ⋙ res d T ≅
      res d T ⋙ completion d T :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (completedReductionTower T d) (lambda d T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rho d T) (rlim (A := A) T) ≪≫ Functor.associator _ _ _

theorem completedComparison_hom_app (T : Scheme.{t}) (K : d.derived T) :
    (completedComparison d T).hom.app K =
      (lambda d T).hom.app ((completedReductionTower T d).obj K) ≫
        (rlim (A := A) T).map ((rho d T).hom.app K) := by
  simp only [completedComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]

/-- Restriction carries the completed completion unit to the constant completion unit. -/
theorem completedComparison_unit (T : Scheme.{t}) (K : d.derived T) :
    (res d T).map (d.completionUnit T K) ≫ (completedComparison d T).hom.app K =
      (unit d T).app ((res d T).obj K) := by
  rw [completedComparison_hom_app]
  exact rho_unit_second d T K

/-- The completed completion unit as a natural transformation. -/
def completedUnitNatTrans (T : Scheme.{t}) :
    𝟭 (d.derived T) ⟶ completedReductionTower T d ⋙ completedRlim T (d.completedRing T) :=
  (d.constantRlimAdjunction T).unit ≫
    Functor.whiskerRight (completedReductionAugmentation d T)
      (completedRlim T (d.completedRing T))

theorem completedUnitNatTrans_app (T : Scheme.{t}) (K : d.derived T) :
    (completedUnitNatTrans d T).app K = d.completionUnit T K := rfl

/-- The completed quotient completion inverts its own unit. -/
theorem completion_map_completionUnit_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((completedReductionTower T d ⋙ completedRlim T (d.completedRing T)).map
      (d.completionUnit T K)) := by
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have hr := quotient_reflection d T
  have heq : C.map (d.completionUnit T K) = d.completionUnit T (C.obj K) := by
    apply (hr.2 K (C.obj (C.obj K)) (hr.1 (C.obj K))).1
    have hn := (completedUnitNatTrans d T).naturality (d.completionUnit T K)
    simp only [Functor.id_map, completedUnitNatTrans_app] at hn
    exact hn.symm
  rw [heq]
  exact hr.1 K

/-- The constant completion of a restricted object is complete. -/
theorem unit_completion_res_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((unit d T).app ((completion d T).obj ((res d T).obj K))) := by
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have : IsIso (d.completionUnit T (C.obj K)) := (quotient_reflection d T).1 K
  have : IsIso ((unit d T).app ((res d T).obj (C.obj K))) := by
    rw [← completedComparison_unit]
    infer_instance
  exact @unit_isIso_of_iso _ _ (completion d T) (unit d T) _ _
    ((completedComparison d T).app K).symm this

/-- The constant completion inverts the unit at a restricted object. -/
theorem completion_map_unit_res_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((completion d T).map ((unit d T).app ((res d T).obj K))) := by
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have := completion_map_completionUnit_isIso d T K
  rw [← completedComparison_unit, Functor.map_comp]
  have hn := (completedComparison d T).hom.naturality (d.completionUnit T K)
  have : IsIso ((C ⋙ res d T).map (d.completionUnit T K)) := by
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((completedComparison d T).hom.app K ≫
      (res d T ⋙ completion d T).map (d.completionUnit T K)) := by
    rw [← hn]
    infer_instance
  have : IsIso ((res d T ⋙ completion d T).map (d.completionUnit T K)) :=
    IsIso.of_isIso_comp_left ((completedComparison d T).hom.app K) _
  have : IsIso ((completion d T).map ((res d T).map (d.completionUnit T K))) := by
    rwa [Functor.comp_map] at this
  infer_instance

/-- Precomposition with a unit is injective into objects with invertible unit, once the
endofunctor inverts the given unit. -/
theorem precomp_unit_injective {C : Type*} [Category C] {G : C ⥤ C} (η : 𝟭 C ⟶ G)
    {X Y : C} (hX : IsIso (G.map (η.app X))) (hY : IsIso (η.app Y))
    {g₁ g₂ : G.obj X ⟶ Y} (h : η.app X ≫ g₁ = η.app X ≫ g₂) : g₁ = g₂ := by
  have hG : G.map g₁ = G.map g₂ := by
    apply (cancel_epi (G.map (η.app X))).mp
    rw [← G.map_comp, ← G.map_comp, h]
  apply (cancel_mono (η.app Y)).mp
  have h₁ := η.naturality g₁
  have h₂ := η.naturality g₂
  simp only [Functor.id_map, Functor.id_obj] at h₁ h₂
  rw [h₁, h₂, hG]

/-- Precomposition with a map inverted by a reflection-type endofunctor is bijective into
every object of the reflecting class. -/
theorem precomp_bijective_of_isIso_map {C : Type*} [Category C] (G : C ⥤ C) (η : 𝟭 C ⟶ G)
    (S : C → Prop)
    (hb : ∀ X Z, S Z → Function.Bijective (fun a : G.obj X ⟶ Z ↦ η.app X ≫ a))
    {X Y : C} (f : X ⟶ Y) (hf : IsIso (G.map f)) (Z : C) (hZ : S Z) :
    Function.Bijective (fun a : Y ⟶ Z ↦ f ≫ a) := by
  have := hf
  have hn (a : G.obj Y ⟶ Z) : f ≫ η.app Y ≫ a = η.app X ≫ G.map f ≫ a := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact η.naturality f
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := (hb Y Z hZ).2 a
    obtain ⟨b', rfl⟩ := (hb Y Z hZ).2 b
    simp only at hab ⊢
    rw [hn, hn] at hab
    rw [(cancel_epi (G.map f)).mp ((hb X Z hZ).1 hab)]
  · intro c
    obtain ⟨c', rfl⟩ := (hb X Z hZ).2 c
    refine ⟨η.app Y ≫ inv (G.map f) ≫ c', ?_⟩
    simp only
    rw [hn, IsIso.hom_inv_id_assoc]

section CompleteEquivalence

set_option allowUnsafeReducibility true in
attribute [local semireducible] reductionModule completedReductionModuleTowerFunctor reduction

/-- Derived scalar extension along the constant-to-completed coefficient map, as a left
adjoint of the derived restriction `res`. -/
def resAdjunction (T : Scheme.{t}) : pbcDerivedExtend (exchangeScalar d T) ⊣ res d T :=
  pbcDerivedScalarAdjunction (exchangeScalar d T)

set_option backward.isDefEq.respectTransparency true in
/-- At every finite quotient level the ordinary scalar-extension unit becomes invertible:
the balancing map identifies `F_n ⊗ (B ⊗ M)` with `F_n ⊗ M`, and the strict balancing
comparison `ordinaryRho` identifies the two finite reductions. -/
theorem level_map_scalarUnit_isIso (T : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) (i : ℤ) :
    IsIso ((level d T n).map
      ((pbcScalarAdjunction (exchangeScalar d T)).unit.app (P.X i))) := by
  let φ := exchangeScalar d T
  let M := P.X i
  let β := (HomologicalComplex.eval _ _ i).mapIso
    (asIso (reductionBalance T φ (d.projection T n) (quotient d T n) rfl P))
  let e : (level d T n).obj ((pbcExtend φ ⋙ pbcRestrict φ).obj M) ≅ (level d T n).obj M :=
    ((ordinaryRho_existsUnique d T).exists.choose.app
      ((reductionChange T φ).obj M)).app (op n) ≪≫ (reductionRestrict T (quotient d T n)).mapIso β
  have hc : (level d T n).map ((pbcScalarAdjunction φ).unit.app M) ≫ e.hom = 𝟙 _ := by
    apply level_hom_ext T (quotient d T n) M
    intro U s x
    have h₁ := tensorSection_map d T n ((pbcScalarAdjunction φ).unit.app M) U s x
    have h₂ : ((pbcScalarAdjunction φ).unit.app M).val.app U x =
        reductionTensorSection T φ M U 1 x := by
      unfold pbcScalarAdjunction
      exact (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
    have h₃ := (ordinaryRho_existsUnique d T).exists.choose_spec
      ((reductionChange T φ).obj M) n U s (reductionTensorSection T φ M U 1 x)
    have h₄ := reductionBalance_tmul T φ (d.projection T n) (quotient d T n) rfl P i U s 1 x
    simp only [map_one, mul_one] at h₄
    rw [h₂] at h₁
    with_unfolding_all
      exact (congrArg (fun w ↦ e.hom.val.app U w) h₁).trans
        ((congrArg (fun w ↦ β.hom.val.app U w) h₃).trans h₄)
  have hc' : e.hom ≫ (level d T n).map ((pbcScalarAdjunction φ).unit.app M) = 𝟙 _ := by
    rw [(Iso.comp_hom_eq_id e).1 hc, Iso.hom_inv_id]
  exact ⟨⟨e.hom, hc, hc'⟩⟩

/-- The strict quotient diagram inverts the ordinary scalar-extension unit on complexes. -/
theorem reductionModule_map_scalarUnit_isIso (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    IsIso (((reductionModule d T).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction (exchangeScalar d T)).unit
        (.up ℤ)).app P)) := by
  have (i : ℤ) : IsIso ((((reductionModule d T).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction (exchangeScalar d T)).unit
        (.up ℤ)).app P)).f i) := by
    have (n : ℕᵒᵖ) : IsIso (((reductionModule d T).map
        ((pbcScalarAdjunction (exchangeScalar d T)).unit.app (P.X i))).app n) :=
      level_map_scalarUnit_isIso d T n.unop P i
    have h : IsIso ((reductionModule d T).map
        ((pbcScalarAdjunction (exchangeScalar d T)).unit.app (P.X i))) :=
      NatIso.isIso_of_isIso_app _
    exact h
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The derived quotient reduction inverts the localization of a chain map between K-flat
complexes once the strict quotient diagram inverts it. -/
theorem reduction_map_Q_isIso (T : Scheme.{t})
    {P P' : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ} (g : P ⟶ P')
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A) P')
    (hg : IsIso (((reductionModule d T).mapHomologicalComplex (.up ℤ)).map g)) :
    IsIso ((reduction d T).map (DerivedCategory.Q.map g)) := by
  let N := complexCounitNat (reductionModule d T) (reductionData d T).reduction
    (reductionData d T).counit
  have : IsIso (N.app P) := by
    rw [complexCounitNat_app]
    exact (reductionData d T).complexCounit_isIso P hP
  have : IsIso (N.app P') := by
    rw [complexCounitNat_app]
    exact (reductionData d T).complexCounit_isIso P' hP'
  have : IsIso (((reductionModule d T).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).map g) := by
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((DerivedCategory.Q ⋙ (reductionData d T).reduction).map g ≫ N.app P') := by
    rw [N.naturality g]
    infer_instance
  have : IsIso ((DerivedCategory.Q ⋙ (reductionData d T).reduction).map g) :=
    IsIso.of_isIso_comp_right _ (N.app P')
  rw [Functor.comp_map] at this
  exact this

/-- The quotient reduction inverts the unit of derived scalar extension. -/
theorem reduction_map_resAdjunction_unit_isIso (T : Scheme.{t}) (X : D (A := A) T) :
    IsIso ((reduction d T).map ((resAdjunction d T).unit.app X)) := by
  let φ := exchangeScalar d T
  let adj := resAdjunction d T
  let Q : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ ⥤ D (A := A) T :=
    DerivedCategory.Q
  obtain ⟨L, s, hL, hflat, hs, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage X)
  have := hs
  let e : Q.obj L ≅ X := asIso (Q.map s) ≪≫ Q.objObjPreimageIso X
  have hX : adj.unit.app X = e.inv ≫ adj.unit.app (Q.obj L) ≫
      (pbcDerivedExtend φ ⋙ res d T).map e.hom := by
    rw [← adj.unit.naturality e.hom, Functor.id_map, Iso.inv_hom_id_assoc]
  let g := (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app L
  have hsp : adj.unit.app (Q.obj L) ≫ (res d T).map (pbcComplexCounit φ L) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj L) = Q.map g := by
    with_unfolding_all exact (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec L hL
  have : IsIso (pbcComplexCounit φ L) := by
    have := pbcExtensionCounit_isIso φ L hL
    unfold pbcComplexCounit
    infer_instance
  have hU : adj.unit.app (Q.obj L) = Q.map g ≫ inv ((res d T).map (pbcComplexCounit φ L) ≫
      (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj L)) := by
    rw [← hsp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hP' : CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing T A)
      (((pbcExtend φ ⋙ pbcRestrict φ).mapHomologicalComplex (.up ℤ)).obj L) :=
    (SheafOfModules.isKFlat_restrictScalars_of_flat φ (orderedScalarFlat d T) _
      (reductionChange_isKFlat T φ L hL hflat)).1
  have : IsIso ((reduction d T).map (Q.map g)) :=
    reduction_map_Q_isIso d T g hL hP' (reductionModule_map_scalarUnit_isIso d T L)
  rw [hX, hU]
  simp only [Functor.map_comp]
  infer_instance

/-- Derived scalar extension followed by restriction has the same quotient completion: the
completion of the counit of `resAdjunction` is invertible. -/
theorem completion_map_resAdjunction_counit_isIso (T : Scheme.{t}) (K : d.derived T) :
    IsIso ((completedReductionTower T d ⋙ completedRlim T (d.completedRing T)).map
      ((resAdjunction d T).counit.app K)) := by
  let adj := resAdjunction d T
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have hr : (res d T).ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction (𝟙 T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeScalar d T) (exchangeScalar d T) (exchangeConstantIso (𝟙 T) A)
      (d.integralRingIso (𝟙 T)) (exchangeScalar_comm d (𝟙 T))).1
  have := reduction_map_resAdjunction_unit_isIso d T ((res d T).obj K)
  have ht : (reduction d T).map (adj.unit.app ((res d T).obj K)) ≫
      (reduction d T).map ((res d T).map (adj.counit.app K)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, adj.right_triangle_components]
    exact (reduction d T).map_id _
  have : IsIso ((reduction d T).map ((res d T).map (adj.counit.app K))) := by
    rw [IsIso.eq_inv_of_hom_inv_id ht]
    infer_instance
  have : IsIso ((res d T ⋙ completion d T).map (adj.counit.app K)) := by
    rw [Functor.comp_map]
    unfold completion
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((C ⋙ res d T).map (adj.counit.app K)) :=
    (NatIso.isIso_map_iff (completedComparison d T) _).2 this
  rw [Functor.comp_map] at this
  exact isIso_of_reflects_iso _ (res d T)

/-- Restriction is bijective on morphisms into a quotient-complete object. -/
theorem res_map_bijective (T : Scheme.{t}) (K K' : d.derived T)
    (hK' : d.TowerComplete T K') :
    Function.Bijective (fun f : K ⟶ K' ↦ (res d T).map f) := by
  let adj := resAdjunction d T
  have hb := precomp_bijective_of_isIso_map
    (completedReductionTower T d ⋙ completedRlim T (d.completedRing T))
    (completedUnitNatTrans d T) (d.TowerComplete T)
    (fun X Z hZ ↦ (quotient_reflection d T).2 X Z hZ) (adj.counit.app K)
    (completion_map_resAdjunction_counit_isIso d T K) K' hK'
  have he : (fun f : K ⟶ K' ↦ (res d T).map f) =
      (adj.homEquiv _ _) ∘ (fun f : K ⟶ K' ↦ adj.counit.app K ≫ f) := by
    funext f
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      Adjunction.right_triangle_components_assoc]
  rw [he]
  exact (adj.homEquiv _ _).bijective.comp hb

/-- Every constant-coefficient complete object is the restriction of a quotient-complete
completed-coefficient object: the completion of its derived scalar extension. -/
theorem res_essSurj (T : Scheme.{t}) (X : D (A := A) T) (hX : IsComplete d T X) :
    ∃ K : d.derived T, d.TowerComplete T K ∧ Nonempty ((res d T).obj K ≅ X) := by
  let adj := resAdjunction d T
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  let K₀ := (pbcDerivedExtend (exchangeScalar d T)).obj X
  have : IsIso ((completion d T).map (adj.unit.app X)) := by
    have := reduction_map_resAdjunction_unit_isIso d T X
    unfold completion
    rw [Functor.comp_map]
    infer_instance
  have : IsIso ((unit d T).app X) := hX
  exact ⟨C.obj K₀, (quotient_reflection d T).1 K₀, ⟨(completedComparison d T).app K₀ ≪≫
    (asIso ((completion d T).map (adj.unit.app X))).symm ≪≫ (asIso ((unit d T).app X)).symm⟩⟩

end CompleteEquivalence

/-- Restriction gives an equivalence on the two full complete subcategories. -/
theorem restriction_complete_equiv (T : Scheme.{t}) :
    ∃ e : AComplete d T ≌ Complete d T,
      Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete d T) ≅
        inclusion d T ⋙ res d T) := by
  let F : AComplete d T ⥤ D (A := A) T := inclusion d T ⋙ res d T
  have : F.Faithful := ⟨fun {K K'} f g h ↦ ObjectProperty.hom_ext _
    ((res_map_bijective d T K.obj K'.obj K'.property).1 h)⟩
  have : F.Full := ⟨fun {K K'} g ↦ by
    obtain ⟨f, hf⟩ := (res_map_bijective d T K.obj K'.obj K'.property).2 g
    exact ⟨ObjectProperty.homMk f, hf⟩⟩
  let G := ObjectProperty.lift (IsComplete d T) F
    (fun K ↦ (restriction_complete_iff d T K.obj).mp K.property)
  have : G.EssSurj := ⟨fun Y ↦ by
    obtain ⟨K, hK, ⟨e⟩⟩ := res_essSurj d T Y.obj Y.property
    exact ⟨⟨K, hK⟩, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  have : G.IsEquivalence := {}
  exact ⟨G.asEquivalence, ⟨ObjectProperty.liftCompιIso _ _ _⟩⟩

theorem restriction_complete (T : Scheme.{t}) :
    (∀ K : d.derived T, d.TowerComplete T K ↔ IsComplete d T ((res d T).obj K)) ∧
      ∃ e : AComplete d T ≌ Complete d T,
        Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete d T) ≅
          inclusion d T ⋙ res d T) := by
  exact ⟨restriction_complete_iff d T, restriction_complete_equiv d T⟩

/-- The ordinary-to-completed comparison is the completed completion unit of the ordinary
pullback, through the canonical reduction-tower pullback comparison. -/
theorem ordinaryToCompleted_stratum (K : d.derived V) :
    d.ordinaryToCompleted u K ≫
        (completedRlim U (d.completedRing U)).map ((stratumReductionIso d u).hom.app K) =
      d.completionUnit U ((d.pull u).obj K) := by
  let R := completedRlim U (d.completedRing U)
  unfold AdicCoefficientDatum.ordinaryToCompleted AdicCoefficientDatum.completionUnit
  rw [Category.assoc, ← R.map_comp, Category.assoc, stratumReduction_augmentation d u K]
  rw [← Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.id_comp]
  rfl

/-- The scalar comparison for completed pullback is fixed by the actual completion units. -/
theorem phi_exists :
    ∃ e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u,
      ∀ K : AComplete d V,
        (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e.hom.app K =
          (alpha d u).hom.app K.obj ≫
            (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)) := by
  let R := completedRlim U (d.completedRing U)
  let e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
      inclusion d V ⋙ res d V ⋙ completePull d u :=
    Functor.isoWhiskerLeft (inclusion d V)
      (Functor.isoWhiskerRight (Functor.isoWhiskerRight (stratumReductionIso d u) R)
          (res d U) ≪≫
        Functor.isoWhiskerLeft (d.pull u) (completedComparison d U) ≪≫
        Functor.isoWhiskerRight (alpha d u) (completion d U))
  refine ⟨e, fun K ↦ ?_⟩
  simp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ObjectProperty.ι_obj]
  rw [← Category.assoc, ← Functor.map_comp, ordinaryToCompleted_stratum,
    ← Category.assoc, completedComparison_unit]
  exact ((unit d U).naturality ((alpha d u).hom.app K.obj)).symm

/-- The completed pullback/scalar comparison is determined by its unit equation. -/
theorem phi_unique
    {e₁ e₂ : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u}
    (h₁ : ∀ K : AComplete d V,
      (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e₁.hom.app K =
        (alpha d u).hom.app K.obj ≫
          (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)))
    (h₂ : ∀ K : AComplete d V,
      (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e₂.hom.app K =
        (alpha d u).hom.app K.obj ≫
          (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj))) :
    e₁ = e₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  let j : (res d U).obj ((d.completedPull u).obj K.obj) ≅
      (completion d U).obj ((res d U).obj ((d.pull u).obj K.obj)) :=
    (res d U).mapIso ((completedRlim U (d.completedRing U)).mapIso
      ((stratumReductionIso d u).app K.obj)) ≪≫
      (completedComparison d U).app ((d.pull u).obj K.obj)
  have hj : (res d U).map (d.ordinaryToCompleted u K.obj) ≫ j.hom =
      (unit d U).app ((res d U).obj ((d.pull u).obj K.obj)) := by
    rw [← completedComparison_unit, ← ordinaryToCompleted_stratum d u K.obj, Functor.map_comp]
    simp only [j, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  have hY : IsIso ((unit d U).app ((completePull d u).obj ((res d V).obj K.obj))) := by
    have := unit_completion_res_isIso d U ((d.pull u).obj K.obj)
    exact @unit_isIso_of_iso _ _ (completion d U) (unit d U) _ _
      ((completion d U).mapIso ((alpha d u).app K.obj)).symm this
  have key : j.inv ≫ e₁.hom.app K = j.inv ≫ e₂.hom.app K := by
    apply precomp_unit_injective (unit d U)
      (completion_map_unit_res_isIso d U ((d.pull u).obj K.obj)) hY
    rw [← hj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (h₁ K).trans (h₂ K).symm
  exact (cancel_epi j.inv).mp key

theorem phi_existsUnique :
    ∃! e : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
        inclusion d V ⋙ res d V ⋙ completePull d u,
      ∀ K : AComplete d V,
        (res d U).map (d.ordinaryToCompleted u K.obj) ≫ e.hom.app K =
          (alpha d u).hom.app K.obj ≫
            (unit d U).app ((pull (A := A) u).obj ((res d V).obj K.obj)) := by
  obtain ⟨e, he⟩ := phi_exists d u
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact (phi_unique d u he he').symm

/-- The completed pullback/scalar isomorphism, retaining its completion-unit equation. -/
def phi : inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
    inclusion d V ⋙ res d V ⋙ completePull d u := (phi_existsUnique d u).exists.choose

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The specified completed-coefficient source reconstruction. -/
def sourceReconstruction (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    ((d.reductionTowerPullbackIso g).app ((d.push f).obj K))

/-- The source comparison s a is exactly the ordered projection-formula comparison. -/
def sourceA (K : d.derived X) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    (d.towerH (f := f) (f' := f') (g := g) (g' := g') K)

/-- The specified direct-image/limit comparison c a. -/
def targetA (K : d.derived X) :=
  (d.directImageRlimIso f').app
    ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- The left corner comparison includes the image of the same strict reduction rho. -/
def beta (K : d.derived X) :=
  (exchangeCornerB d f g).app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g).mapIso
      ((exchangeConstantPush (A := A) f).mapIso ((rho d X).app K))

/-- The right corner comparison includes the image of that same strict reduction rho. -/
def delta (K : d.derived X) :=
  (exchangeCornerD d g' f').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPush (A := A) f').mapIso
      ((exchangeConstantPull (A := A) g').mapIso ((rho d X).app K))

/-- The scalar comparison at M uses finite reduction, ordinary pullback and chi f. -/
def rhoM (K : d.derived X) :=
  (rho d Y').app ((d.pull g).obj ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((alpha d g).app ((d.push f).obj K)) ≪≫
    (reduction d Y').mapIso ((pull (A := A) g).mapIso ((chi d f).app K))

/-- The pulled-back strict reduction comparison retains its full diagram, not just levels. -/
def rhoPull (K : d.derived X) :=
  (exchangeResPull d g').app ((completedReductionTower X d).obj K) ≪≫
    (exchangeConstantPull (A := A) g').mapIso ((rho d X).app K)

/-- The source scalar identification, with phi evaluated at the complete direct image. -/
def iotaS (K : d.derived X) (hK : d.TowerComplete X K) :=
  (phi d g).app ⟨(d.push f).obj K, d.push_complete f K hK⟩ ≪≫
    (completePull d g).mapIso ((chi d f).app K)

/-- The target scalar identification is chi followed by direct image of phi. -/
def iotaT (K : d.derived X) (hK : d.TowerComplete X K) :=
  (chi d f').app ((d.completedPull g').obj K) ≪≫
    (push (A := A) f').mapIso ((phi d g').app ⟨K, hK⟩)

/-- Source functor for the normalized equation, on the full derived-complete category. -/
def normalizedSource := inclusion d X ⋙ d.push f ⋙ d.completedPull g ⋙ res d Y'

/-- Target functor for the normalized equation in constant coefficients. -/
def normalizedTarget := inclusion d X ⋙ res d X ⋙ completePull d g' ⋙ push (A := A) f'

/-- The restricted raw ordered construction followed by the specified target comparison. -/
def rawComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (res d Y').map (d.completedExchange sq K.obj) ≫
    (iotaT (g' := g') (f' := f') d K.obj K.property).hom

/-- The specified constant strict mate, conjugated by s, t and the source scalar map. -/
def constantComponent (sq : ChosenCartesianSquare g' f' f g) (K : AComplete d X) :
    (normalizedSource (f := f) (g := g) d).obj K ⟶
      (normalizedTarget (g' := g') (f' := f') d).obj K :=
  (iotaS (f := f) (g := g) d K.obj K.property).hom ≫
    (S (f := f) (g := g) d ((res d X).obj K.obj)).hom ≫
    (rlim (A := A) Y').map ((exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
      ((reduction d X).obj ((res d X).obj K.obj))) ≫
    (T (f' := f') (g' := g') d ((res d X).obj K.obj)).inv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Both displayed composites are natural for every morphism of complete inputs. -/
theorem normalized_naturality (sq : ChosenCartesianSquare g' f' f g)
    (K L : AComplete d X) (a : K ⟶ L) :
    (normalizedSource (f := f) (g := g) d).map a ≫ rawComponent d sq L =
      rawComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a ∧
    (normalizedSource (f := f) (g := g) d).map a ≫ constantComponent d sq L =
      constantComponent d sq K ≫ (normalizedTarget (g' := g') (f' := f') d).map a := by
  let piA (U V : Scheme.{t}) (u : U ⟶ V) :
      d.push u ⋙ completedReductionTower V d ≅
        completedReductionTower U d ⋙ d.towerPush u :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection u K))
      (fun {K L} a ↦ (d.towerProjection_properties u K).2.1 L a)
  let e : d.push f ⋙ d.completedPull g ⟶ d.completedPull g' ⋙ d.push f' :=
    Functor.whiskerRight (Functor.isoWhiskerRight (piA X Y f) (d.towerPull g)).hom
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerRight (exchangeStrictNatTrans d sq)
        (completedRlim Y' (d.completedRing Y')) ≫
      Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
        (d.directImageRlimIso f').inv
  let it : inclusion d X ⋙ d.completedPull g' ⋙ d.push f' ⋙ res d Y' ≅
      normalizedTarget (g' := g') (f' := f') d :=
    Functor.isoWhiskerLeft (inclusion d X ⋙ d.completedPull g') (chi d f') ≪≫
      Functor.isoWhiskerRight (phi d g') (push (A := A) f')
  constructor
  · exact (Functor.whiskerLeft (inclusion d X)
      (Functor.whiskerRight e (res d Y')) ≫ it.hom).naturality a
  · let aj := exchangeTowerAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let ar := proEtaleRingDerivedAdjunction f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A)
    let pi0 := (mateEquiv ar aj
      (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom))
    have hpi (M : D (A := A) X) : pi0.app M = projection d f M := by
      apply (aj.homEquiv _ _).symm.injective
      change (aj.homEquiv _ _).symm (pi0.app M) =
        (aj.homEquiv _ _).symm ((aj.homEquiv _ _)
          ((reductionPullIso d f).hom.app ((push (A := A) f).obj M) ≫
            (reduction d X).map (ar.counit.app M)))
      rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
      exact mateEquiv_counit ar aj
        (TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom) M
    let p0 : push (A := A) f ⋙ reduction d Y ≅
        reduction d X ⋙ exchangeConstantPush (A := A) f :=
      NatIso.ofComponents (fun M ↦ asIso (projection d f M)) (by
        intro M N b
        simpa only [asIso_hom, ← hpi] using pi0.naturality b)
    let h0 := Functor.isoWhiskerLeft (push (A := A) f) (reductionPullIso d g).symm ≪≫
      Functor.isoWhiskerRight p0 (exchangeConstantPull (A := A) g)
    let s0 := Functor.isoWhiskerRight h0 (rlim (A := A) Y')
    let t0 := Functor.isoWhiskerLeft (reduction d X)
      (Functor.isoWhiskerLeft (exchangeConstantPull (A := A) g')
        (directLimitIso (A := A) f'))
    let rec0 : completePull d g' ≅
        reduction d X ⋙ exchangeConstantPull (A := A) g' ⋙ rlim (A := A) X' :=
      Functor.isoWhiskerRight (reductionPullIso d g').symm (rlim (A := A) X')
    let tt := Functor.isoWhiskerRight rec0 (push (A := A) f') ≪≫ t0
    let pushed : AComplete d X ⥤ AComplete d Y :=
      ObjectProperty.lift (d.TowerComplete Y) (inclusion d X ⋙ d.push f)
        (fun M ↦ d.push_complete f M.obj M.property)
    let src : normalizedSource (f := f) (g := g) d ≅
        inclusion d X ⋙ res d X ⋙ push (A := A) f ⋙ completePull d g :=
      Functor.isoWhiskerLeft pushed (phi d g) ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft (inclusion d X) (chi d f))
          (completePull d g)
    let cc := src.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) s0.hom ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X ⋙ reduction d X)
        (Functor.whiskerRight
          (exchangeConstantSquare (A := A) sq).exchangeTowerMate (rlim (A := A) Y')) ≫
      Functor.whiskerLeft (inclusion d X ⋙ res d X) tt.inv
    exact cc.naturality a

/-- The raw ordered exchange as an actual natural transformation after scalar restriction. -/
def rawNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := rawComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).1

/-- The specified constant-coefficient ordered expression as a natural transformation. -/
def constantNormalized (sq : ChosenCartesianSquare g' f' f g) :
    normalizedSource (f := f) (g := g) d ⟶ normalizedTarget (g' := g') (f' := f') d where
  app K := constantComponent d sq K
  naturality K L a := (normalized_naturality d sq K L a).2

end AlgebraicGeometry.Scheme.OrderedExchange
