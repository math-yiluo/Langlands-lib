/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
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
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
public import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import WeilConjectures.RingTheory.LimitFlatModules
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionFinitePullSupplement
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteConstantSliceComparison
import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteScalarTransport
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Relative finite coefficients on the equivalent small site

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03A0
* Cohomology on Sites, Tags 06YY and 094I
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem finiteLocalModels_of_iso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type (u + 1)) [CommRing B]
    {F G : SheafOfModules.{u + 1} (SheafOfModules.constantCoefficientRing J B)}
    (e : F ≅ G) (h : SheafOfModules.IsLocallyConstantFiniteTypeModules J B F) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules J B G := by
  intro V
  obtain ⟨S, hS, hs⟩ := h V
  refine ⟨S, hS, fun W f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hs W f hf
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ W).mapIso e.symm ≪≫ i⟩⟩

private theorem finiteLocalModels_iso_iff
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type (u + 1)) [CommRing B]
    {F G : SheafOfModules.{u + 1} (SheafOfModules.constantCoefficientRing J B)}
    (e : F ≅ G) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules J B F ↔
      SheafOfModules.IsLocallyConstantFiniteTypeModules J B G :=
  ⟨finiteLocalModels_of_iso J B e, finiteLocalModels_of_iso J B e.symm⟩

private theorem relativeFiniteLisse_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) :
    IsRelativelyFiniteLisseModule g B F ↔
      SheafOfModules.IsLocallyConstantFiniteTypeModules (proEtaleModelTopology Y) B
        ((relativeFiniteModelModules g B).obj F) := by
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_functor
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsDenseSubsite
      (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsDenseSubsite
      (proEtaleModelTopology Y) (ProEt.topology Y) :=
    inferInstanceAs (AsSmall.down.IsDenseSubsite _ _)
  have : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsDenseSubsite
      (ProEt.topology Y) (proEtaleModelTopology Y) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsDenseSubsite
      (ProEt.topology Y) (proEtaleModelTopology Y))
  constructor
  · rintro ⟨S, hS, hs⟩ V
    let S' := S.pullback (terminal.from (AsSmall.down.obj V))
    refine ⟨S'.functorPullback AsSmall.down, ?_, fun W a ha ↦ ?_⟩
    · exact AsSmall.down.cover_lift (proEtaleModelTopology Y) (ProEt.topology Y)
        ((ProEt.topology Y).pullback_stable _ hS)
    · obtain ⟨M, hM, hm⟩ := hs (AsSmall.down.obj W)
        (AsSmall.down.map a ≫ terminal.from (AsSmall.down.obj V)) ha
      have : Finite M := hM
      exact ⟨M, inferInstance, (relativeFiniteConstantSliceComparison g B F M W).mp hm⟩
  · intro hF
    obtain ⟨S, hS, hs⟩ := hF (AsSmall.up.obj (⊤_ Y.ProEt))
    refine ⟨S.functorPullback AsSmall.up, ?_, fun V a ha ↦ ?_⟩
    · exact AsSmall.up.cover_lift (ProEt.topology Y) (proEtaleModelTopology Y) hS
    · obtain ⟨M, hM, hm⟩ := hs (AsSmall.up.obj V) (AsSmall.up.map a) ha
      have : Module.Finite B M := hM
      exact ⟨M, Module.finite_of_finite B,
        (relativeFiniteConstantSliceComparison g B F M (AsSmall.up.obj V)).mpr hm⟩

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Exact small-site models preserve relative finite lissity and coefficient extension. -/
theorem exists_relative_finite_coefficient_model {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] [Finite B] [Finite R]
    (f : B →+* R)
    (K : DerivedCategory (pbcModules X (adicLisseConstantRing X B))) :
    let J := proEtaleModelTopology Y
    ∃ L : CategoryTheory.ConstantCompletion.D
        (CategoryTheory.ConstantCompletion.constant J B),
      (∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor
          (pbcModules X (adicLisseConstantRing X B)) q).obj K) →
        IsZero ((coefficientModelCohomology _ q).obj L)) ∧
      (∀ q : ℤ, IsRelativelyFiniteLisseModule g B
          ((DerivedCategory.homologyFunctor
              (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) q).obj
            ((adicTowerPullback g (adicLisseConstantRing X B)).obj K)) ↔
        SheafOfModules.IsLocallyConstantFiniteTypeModules J B
          ((coefficientModelCohomology _ q).obj L)) ∧
      (∀ q : ℤ, IsRelativelyFiniteLisseModule g R
          ((DerivedCategory.homologyFunctor
              (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X R))) q).obj
            ((adicTowerPullback g (adicLisseConstantRing X R)).obj
              ((pbcDerivedExtend ((constantSheaf (ProEt.topology X)
                CommRingCat.{u + 1}).map (CommRingCat.ofHom f))).obj K))) ↔
        SheafOfModules.IsLocallyConstantFiniteTypeModules J R
          ((coefficientModelCohomology _ q).obj
            ((adicFiniteExtension J f).obj L))) := by
  let P := (adicTowerPullback g (adicLisseConstantRing X B)).obj K
  let L := (relativeFiniteModelDerived g B).obj P
  refine ⟨L, ?_, ?_, ?_⟩
  · intro q hq
    let F := proEtaleRingModulePullback g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)
    have hp : IsZero ((DerivedCategory.homologyFunctor _ q).obj P) :=
      (F.map_isZero hq).of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm
    exact ((relativeFiniteModelModules g B).map_isZero hp).of_iso
      (relativeFiniteModelHomologyIso g B P q).symm
  · intro q
    exact (relativeFiniteLisse_iff g B _).trans
      (finiteLocalModels_iso_iff (proEtaleModelTopology Y) B
        (relativeFiniteModelHomologyIso g B P q))
  · intro q
    obtain ⟨e⟩ := relativeFiniteScalarTransport g f
    let Kr := (pbcDerivedExtend ((constantSheaf (ProEt.topology X)
      CommRingCat.{u + 1}).map (CommRingCat.ofHom f))).obj K
    let Pr := (adicTowerPullback g (adicLisseConstantRing X R)).obj Kr
    let eh := relativeFiniteModelHomologyIso g R Pr q ≪≫
      (coefficientModelCohomology _ q).mapIso (e.app K)
    exact (relativeFiniteLisse_iff g R _).trans
      (finiteLocalModels_iso_iff (proEtaleModelTopology Y) R eh)

end AlgebraicGeometry.Scheme
