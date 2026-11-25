/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulLimitComparison
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
import WeilConjectures.CategoryTheory.RingedKoszulDualizable
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Comparing the published Koszul fiber with Cech internal Hom

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, and sites-cohomology.tex, Tags 0941 and 0A0A.
(blueprint: lem-weil-pbc-completed-fiber-cech-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The published Koszul fiber is Cech internal Hom, with its specified unit.
Source: Stacks Project, Tag 0A0E
(blueprint: lem-weil-pbc-completed-fiber-cech-comparison).
Proof: compare the explicit fiber with the prescribed strict derived inverse limit.
The existing single-site Cech--Koszul theorem identifies that strict limit with
Cech internal Hom and carries the Cech unit to the strict unit. Compose the two
isomorphisms and cancel the second unit equation. -/
theorem completed_fiber_cech_comparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let O := completedCechRing X d
    let F := completedCechDerivedEquiv X d
    let b := fun i ↦ completedCechScalar X d (a i)
    ∃ e : F.functor.obj (DerivedCategory.Q.obj (intrinsicCompletionComplex X d r a C)) ≅
        (ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).obj
          (F.functor.obj (DerivedCategory.Q.obj C)),
      F.functor.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) ≫
          e.hom =
        ringedCechCompletionUnit O (ringedExtendedCech O r b).1
          (ringedExtendedCech O r b).2 (F.functor.obj (DerivedCategory.Q.obj C)) := by
  let O := completedCechRing X d
  let F := completedCechDerivedEquiv X d
  let b := fun i ↦ completedCechScalar X d (a i)
  obtain ⟨D, theta, htheta⟩ := exists_ringed_cech_koszul_comparison_on_site O r b
  obtain ⟨e, he⟩ := completed_fiber_strict_limit_comparison X d r a C D
  refine ⟨e ≪≫ (theta.app (F.functor.obj (DerivedCategory.Q.obj C))).symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he, ← htheta]
  change (_ ≫ theta.hom.app _) ≫ theta.inv.app _ = _
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.Scheme
