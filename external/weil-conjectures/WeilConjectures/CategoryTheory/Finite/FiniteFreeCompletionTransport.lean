/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
public import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
public import WeilConjectures.Algebra.Homology.InternalHom
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
public import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
public import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
public import WeilConjectures.CategoryTheory.RingedKoszulDualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
public import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
public import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
public import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
public import WeilConjectures.Algebra.Homology.TelescopeColimit
public import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
public import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
public import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
public import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
public import WeilConjectures.Algebra.Homology.SliceTensorNatural
public import WeilConjectures.Algebra.Homology.SliceModuleSheafification
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
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
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
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
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import all WeilConjectures.CategoryTheory.UnitPowerCompleteness
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeCoordinates
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Flat.FlatScalarKoszulTowerComparisonSupplement
import WeilConjectures.CategoryTheory.Finite.FiniteFreeStrictTowerTransport
import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
import WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferential
import WeilConjectures.Algebra.Homology.HomTensorNaturality
import WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Tactic.Basic
import WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import WeilConjectures.Algebra.Homology.KFlatComparison
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Finite-free scalar extension and Koszul completion

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E; the finite-free
scalar-extension argument extracted from blueprint `prop-weil-pbc-scalar-extension`,
steps 6--7 (blueprint: lem-weil-pbc-finite-free-completion-transport).

The four statements give existence and uniqueness of the unit-normalized comparison,
preservation of local completeness, integer-shift compatibility, the actual tensor-unit
normalization, and balanced tensor composition. Binary composition iterates to any finite
tower. No basis is part of the comparison data.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    {N M : ringedSiteDerived O} (e : N ≅ M)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι M := by
  intro U f hf
  let H := derivedInternalHom (J.over U) (O.over U)
  exact (hN U f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e))).symm

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
variable [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
  (derivedChangeRingIndependentCoefficients J R))]
variable [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
  (derivedChangeRingIndependentCoefficients J S))]

private theorem unit_cancel
    {V : Type*} [Category V] (L : V ⥤ V) (η : ∀ X, X ⟶ L.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y), f ≫ η Y = η X ≫ L.map f)
    (hi : ∀ X, IsIso (L.map (η X)))
    {X Y : V} [IsIso (η Y)] {f g : L.obj X ⟶ Y}
    (h : η X ≫ f = η X ≫ g) : f = g := by
  have := hi X
  have hm : L.map f = L.map g := by
    apply (cancel_epi (L.map (η X))).mp
    simpa only [L.map_comp] using congrArg L.map h
  apply (cancel_mono (η Y)).mp
  rw [hn, hn, hm]

private theorem transport_cancel
    {V W : Type*} [Category V] [Category W]
    (F : V ⥤ W) (L : V ⥤ V) (K : W ⥤ W)
    (η : ∀ X, X ⟶ L.obj X) (ε : ∀ X, X ⟶ K.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y), f ≫ ε Y = ε X ≫ K.map f)
    (hi : ∀ X, IsIso (K.map (ε X)))
    (κ : L ⋙ F ≅ F ⋙ K)
    (hκ : ∀ X, F.map (η X) ≫ κ.hom.app X = ε (F.obj X))
    {X : V} {Y : W} [IsIso (ε Y)] {f g : F.obj (L.obj X) ⟶ Y}
    (h : F.map (η X) ≫ f = F.map (η X) ≫ g) : f = g := by
  have he : ε (F.obj X) ≫ (κ.inv.app X ≫ f) =
      ε (F.obj X) ≫ (κ.inv.app X ≫ g) := by
    rw [← hκ X]
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h
  have hh := unit_cancel K ε hn hi he
  exact (cancel_epi (κ.inv.app X)).mp hh

private theorem principal_reflector
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J O))]
    (t : (O.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation O 1 (fun _ ↦ t)) :
    (∀ X, IsLocallyDerivedRingedIdealComplete O
      (image (ringedKoszulScalar O t).asHom) (image.ι (ringedKoszulScalar O t).asHom)
        (D.completion.obj X)) ∧
    (∀ X Y, IsLocallyDerivedRingedIdealComplete O
      (image (ringedKoszulScalar O t).asHom) (image.ι (ringedKoszulScalar O t).asHom) Y →
      Function.Bijective (fun f : D.completion.obj X ⟶ Y ↦ D.unit X ≫ f)) ∧
    (∀ X, IsIso (D.unit X) ↔ IsLocallyDerivedRingedIdealComplete O
      (image (ringedKoszulScalar O t).asHom) (image.ι (ringedKoszulScalar O t).asHom) X) := by
  obtain ⟨D₀, hc, hb, hi, _⟩ := ringedKoszulCompletionReflector O 1 (fun _ ↦ t)
    (image (ringedKoszulScalar O t).asHom) (image.ι (ringedKoszulScalar O t).asHom)
    (principal_generators O t)
  obtain ⟨θ₀, hθ₀⟩ := exists_ringed_cech_koszul_hom_limit_comparison O 1 (fun _ ↦ t) D₀
  obtain ⟨θ, hθ⟩ := exists_ringed_cech_koszul_hom_limit_comparison O 1 (fun _ ↦ t) D
  let k := θ₀.symm ≪≫ θ
  have hk (X : ringedSiteDerived O) : D₀.unit X ≫ k.hom.app X = D.unit X := by
    rw [← hθ₀ X]
    simp only [k, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    exact hθ X
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact complete_of_iso O _ _ (k.app X) (hc X)
  · intro X Y hY
    constructor
    · intro f g h
      apply (cancel_epi (k.hom.app X)).mp
      apply (hb X Y hY).1
      simpa only [← Category.assoc, hk] using h
    · intro f
      obtain ⟨g, hg⟩ := (hb X Y hY).2 f
      refine ⟨k.inv.app X ≫ g, ?_⟩
      rw [← hk]
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hg
  · intro X
    rw [← hk, isIso_comp_right_iff]
    exact hi X

private theorem finite_free_flat
    (A : SystemScalarModel.{u, u, u} a)
    (hfree : ∃ d : ℕ, Nonempty
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
          (SheafOfModules.unit (derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R)))) :
    PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor a) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor a) := by
  obtain ⟨d, ⟨e⟩⟩ := hfree
  let e' := (Sigma.reindex (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
    (fun _ : Fin d ↦
      SheafOfModules.unit (derivedChangeRingIndependentCoefficients J R))) ≪≫ e.symm
  obtain ⟨hL, hC, _⟩ := finiteFreeStrictTowerTransport a A.model ⟨d, ⟨e'⟩⟩
  let k := Adjunction.leftAdjointUniq A.ordinaryAdj
    (SheafOfModules.RingedTensor.tensorAdjunction a)
  exact ⟨preservesFiniteLimits_of_natIso k, preservesFiniteColimits_of_natIso k⟩

private theorem restriction_complete_iff
    (hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor a) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor a))
    (t : (R.obj ⋙ forget CommRingCat).sections) (Y : ringedSiteDerived S) :
    IsLocallyDerivedRingedIdealComplete R
      (image (ringedKoszulScalar R t).asHom) (image.ι (ringedKoszulScalar R t).asHom)
      ((FlatScalarKoszul.restrictDerived a).obj Y) ↔
    IsLocallyDerivedRingedIdealComplete S
      (image (ringedKoszulScalar S (FlatScalarKoszul.imageSections a (fun _ : Fin 1 ↦ t) 0)).asHom)
      (image.ι (ringedKoszulScalar S
        (FlatScalarKoszul.imageSections a (fun _ : Fin 1 ↦ t) 0)).asHom) Y := by
  obtain ⟨_, DB, DR, _, _, γ, _, _, hγ⟩ :=
    FlatScalarKoszul.flatScalarKoszulTowerComparison a hflat 1 (fun _ ↦ t)
  have hu := hγ.2.2.2.2.2.1
  have hR := (principal_reflector R t DR).2.2
  have hS := (principal_reflector S
    (FlatScalarKoszul.imageSections a (fun _ : Fin 1 ↦ t) 0) DB).2.2
  rw [← hR, ← hS, ← hu, isIso_comp_right_iff]
  have : (FlatScalarKoszul.restrictDerived a).ReflectsIsomorphisms :=
    siteDerivedRestrictScalars_reflectsIsomorphisms a
  constructor
  · intro h
    let := h
    exact isIso_of_reflects_iso _ (FlatScalarKoszul.restrictDerived a)
  · intro h
    let := h
    infer_instance

end CategoryTheory
