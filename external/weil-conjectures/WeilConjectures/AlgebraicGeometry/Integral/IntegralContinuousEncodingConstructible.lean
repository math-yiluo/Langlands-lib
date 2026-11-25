/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralConstructibleComparison
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalModels
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.IntegralSectionMemberModels
import WeilConjectures.AlgebraicGeometry.IntegralSectionScalarModels
import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalars
import WeilConjectures.AlgebraicGeometry.IntegralSectionRegularScalarsScalar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedRealizationRegularSupplement
import WeilConjectures.AlgebraicGeometry.IntegralConstantSectionProjection
import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientModel
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Category.Profinite.AsLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.Algebra.Category.CommAlgCat.Basic
import WeilConjectures.RingTheory.LimitFlatModules
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.CompactAdicContinuousIdentification
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import Mathlib.Order.Filter.Bases.Basic
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import Mathlib.Order.CompletePartialOrder
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientTerminalSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompleteSectionPredicate
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletedSectionIdeal
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletedSectionRing
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsResidueIdealComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientLocalModels
import WeilConjectures.AlgebraicGeometry.DiscretePointPresentationRefinement
import WeilConjectures.AlgebraicGeometry.PointModelFreeModule
import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import WeilConjectures.AlgebraicGeometry.PointModelPullbackFunctor
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.Data.Int.Interval
import WeilConjectures.AlgebraicGeometry.DiscretePointPresentationTransport
import WeilConjectures.AlgebraicGeometry.CoefficientSliceRestrictionIso
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientChartPullback
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.IntegralSectionCoefficientNaturality
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonModelRealizationSupplement
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.DiscreteConstantPresentationLifting
import WeilConjectures.AlgebraicGeometry.ConstantSliceInternalPresentation
import WeilConjectures.AlgebraicGeometry.ConstantSliceModuleEncoding
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientPullbackCoordinates
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientRingPullback
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientSliceFixedModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ConstantModuleGlobalEncoding
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.DiscreteInternalMatrixLocalLifting
import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.DiscreteSectionCoordinates
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import WeilConjectures.CategoryTheory.FiniteLocalSectionLifts
import Mathlib.Data.Fintype.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
import WeilConjectures.SixFunctors.ProEtale.IntegralSectionProjectionNormalization
import WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.IntegralSectionLocalIsomorphisms
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleSliceOrdinaryComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientSliceComparisonDataSupplement
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralCoefficientComparison
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.AlgebraicGeometry.IntegralContinuousEncodingConstructible

/-! # Constructibility under continuous integral section encoding

## References

* Bhatt--Scholze, Definition 6.8.10
* Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3)
* Stacks 00YV

## Implementation details

In `integralContinuousEncoding_constructible` the coefficient isomorphism need not preserve
chosen scalar coordinates: finite presentations are invariant under arbitrary coefficient
isomorphisms, and the integral finite-local-presentation criterion supplies scalar local models.
-/

@[expose] public section
set_option autoImplicit false
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  Scheme.integralDetailedCoefficientComparison

attribute [local instance 100000] Sheaf.monoidalCategory Sheaf.braidedCategory

private theorem ring_map_isMonHom (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (f : R ⟶ S) :
    IsMonHom ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f) := by
  set_option backward.isDefEq.respectTransparency true in
    exact Sheaf.isMonHom_sheafCompose_map.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) f

private noncomputable def pointIntegerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCondensedRing l E) ≅ Mon.mk (DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e : latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
    RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
      _ _ (fun _ ↦ Iff.rfl)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let c : Profinite.continuousMapRingSheafOfUniverse (latticeCoefficientIntegers l E) ≅
      DerivedNakayama.integerRingSheaf l E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let cAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso c
  have : IsMonHom cAb.hom := Sheaf.isMonHom_sheafCompose_map _ c.hom
  have : IsMonHom cAb.inv := Sheaf.isMonHom_sheafCompose_map _ c.inv
  exact
    { hom := Mon.ofHom cAb.hom
      inv := Mon.ofHom cAb.inv
      hom_inv_id := by apply Mon.Hom.ext; exact cAb.hom_inv_id
      inv_hom_id := by apply Mon.Hom.ext; exact cAb.inv_hom_id }

attribute [local irreducible] pointIntegerIso

private theorem integral_internal_constant_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [EssentiallySmall.{u + 1} X.ProEt] [IsNoetherian X]
    (M : AdicCompletion.Modules l E X)
    (hM : IsConstructibleModuleObject (AdicCompletion.ring l E X) M) :
    IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M := by
  let e := pointIntegerIso l E
  let φ := e.hom.hom
  let ψ := coefficientMap φ X
  have h := integralLfpConstantModelComparison l E X ((Mod.comap ψ).obj M)
  exact (constantModel_comap_iff φ X M).mp
    (h.mp (_root_.constructible_comap ψ hM))

private theorem normalized_transport {C : Type*} [Category C]
    {A B D Z : C} (d : A ⟶ B) (di : B ⟶ A)
    (p : B ⟶ Z) (q : Z ⟶ B) (r : A ⟶ D)
    (hd : d ≫ di = 𝟙 A) (hp : p ≫ q = 𝟙 B) :
    d ≫ p ≫ (q ≫ (di ≫ r)) = r := by
  rw [← Category.assoc p, hp, Category.id_comp, ← Category.assoc, hd, Category.id_comp]

private theorem sectionRingMap_underlying (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (CondensedRing.sectionRingMap X φ)) = φ := by
  rfl

private theorem reconstructedRingIso_underlying (X : Scheme.{u})
    [EssentiallySmall.{u + 1} X.ProEt]
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (CondensedRing.reconstructedRingIso X R).inv = 𝟙 _ := by
  rfl

private theorem map_inv_normalized
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} (e : A ≅ B) (q : F.obj A ⟶ F.obj B)
    (h : F.map e.hom = q) : F.map e.inv ≫ q = 𝟙 (F.obj B) := by
  rw [← h]
  exact (F.mapIso e).inv_hom_id

private noncomputable def transport_chain_iso
    (X : Scheme.{u}) {R₀ R₁ R₂ S₀ S₁ S₂ S₃ S₄ :
      Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    (α : R₀ ⟶ R₁) (β : R₁ ⟶ R₂) (γ : R₂ ⟶ S₄)
    (c₀ : R₀ ≅ S₀) (c₁ : S₀ ≅ S₁) (c₂ : S₁ ≅ S₂)
    (c₃ : S₂ ≅ S₃) (ε : S₃ ⟶ S₄)
    (h : α ≫ β ≫ γ = c₀.hom ≫ c₁.hom ≫ c₂.hom ≫ c₃.hom ≫ ε)
    (M : SheafOfModules.{u + 1} S₄) :
    (SheafOfModules.restrictScalars α).obj
      ((SheafOfModules.restrictScalars β).obj
        ((SheafOfModules.restrictScalars γ).obj M)) ≅
    (CondensedRing.ringModuleEquivalenceOfIso X c₀).functor.obj
      ((CondensedRing.ringModuleEquivalenceOfIso X c₁).functor.obj
        ((CondensedRing.ringModuleEquivalenceOfIso X c₂).functor.obj
          ((CondensedRing.ringModuleEquivalenceOfIso X c₃).functor.obj
            ((SheafOfModules.restrictScalars ε).obj M)))) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    have hr := congrArg
      (fun g : R₀ ⟶ S₄ ↦ (g.hom.app U).hom r) h
    change (ε.hom.app U (c₃.hom.hom.app U (c₂.hom.hom.app U
      (c₁.hom.hom.app U (c₀.hom.hom.app U r))))) • (show M.val.obj U from m) =
      (γ.hom.app U (β.hom.app U (α.hom.app U r))) • (show M.val.obj U from m)
    exact congrArg (fun t ↦ t • (show M.val.obj U from m)) hr.symm
  · intro U V g
    ext m
    rfl

/-- Integral constructibility is preserved by section-action reconstruction and a
coefficient-ring isomorphism. -/
theorem integralContinuousEncoding_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (X : Scheme.{u}) [IsNoetherian X]
    (c : latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      lisseIntegerSheaf l K X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff l K) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (CondensedRing.integralCoeff l K) X) M) :
    IsContinuousConstructible X (latticeCoefficientIntegers l E)
      ((CondensedRing.ringModuleEquivalenceOfIso X
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)).functor.obj
        ((CondensedRing.continuousIntegerModuleEquivalence l K X).functor.obj M)) := by
  classical
  have : EssentiallySmall.{u + 1} X.ProEt := CategoryTheory.essentiallySmallSelf.{0} X.ProEt
  let J := Scheme.ProEt.topology X
  let : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : TotallyDisconnectedSpace K := inferInstance
  let f : Sheaf J CommRingCat.{u + 1} ⥤ Sheaf J RingCat.{u + 1} :=
    sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let b : Sheaf J RingCat.{u + 1} ⥤ Sheaf J Ab.{u + 1} :=
    sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})
  obtain ⟨s, c₀, hc₀⟩ := continuousIntegralCoefficientComparison X l E
  let d : (Scheme.adicLisseForget X).obj
      (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)) ≅
      WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E X :=
    Scheme.integralDetailedCoefficientComparison.{u} X l E
  let δ : f.obj (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      J (AdicCompletion.ring l E X)) ≅
      WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E X :=
    f.mapIso (integralSectionRingIso l E X)
  let cp := eqToIso (congrArg (coefficientRing X) (integralPointMon_eq l E))
  have ha : IsMonHom (integralLimitAbComparison l E X).hom :=
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec.1
  let := ha
  let am := cp ≪≫ Mon.mkIso' (integralLimitAbComparison l E X)
  let ac : AdicCompletion.ring l E X ≅ sfbCompletedIntegersAb l E X :=
    (Mon.forget _).mapIso am
  have hac : IsMonHom ac.hom := am.hom.isMonHom_hom
  let := hac
  let k := (eqToIso (CondensedRing.lisseIntegerSheaf_eq l K X))
  let chart := asIso (chartComparison X (CondensedRing.continuousIntegers l K))
  let w := b.mapIso d.symm ≪≫ b.mapIso (f.mapIso c₀) ≪≫
    b.mapIso (f.mapIso c) ≪≫ b.mapIso (f.mapIso k) ≪≫ chart.symm
  have hw : IsMonHom w.hom := by
    dsimp only [w, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    have : IsMonHom (b.map d.inv) := ring_map_isMonHom X d.inv
    have : IsMonHom (b.map (f.map c₀.hom)) :=
      ring_map_isMonHom X (f.map c₀.hom)
    have : IsMonHom (b.map (f.map c.hom)) :=
      ring_map_isMonHom X (f.map c.hom)
    have : IsMonHom (b.map (f.map k.hom)) :=
      ring_map_isMonHom X (f.map k.hom)
    infer_instance
  let := hw
  let a : AdicCompletion.ring l E X ≅
      condensedRingObj (CondensedRing.integralCoeff l K) X := ac ≪≫ w
  have haa : IsMonHom a.hom := by
    dsimp only [a, Iso.trans_hom]
    infer_instance
  let := haa
  let N := (Mod.comap a.hom).obj M
  have hN : IsConstructibleModuleObject (AdicCompletion.ring l E X) N :=
    _root_.constructible_comap a.hom hM
  have hconst := integral_internal_constant_models l E X N hN
  have hmodels := (integralSectionLocalModels l E X N).mp hconst
  let Q := (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c)).functor.obj
    ((CondensedRing.continuousIntegerModuleEquivalence l K X).functor.obj M)
  let B := (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c₀)).functor.obj Q
  let W := (SheafOfModules.restrictScalars d.hom).obj
    ((integralSectionFunctor l E X).obj N)
  have hn : b.map δ.hom = ac.hom := by
    have hn := (integralSectionRingIso_existsUnique l E X).exists.choose_spec
    change b.map δ.hom = _ at hn
    symm
    dsimp only [ac, am, cp, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    rw [Functor.map_comp]
    change (Mon.forget (Sheaf J Ab.{u + 1})).map (eqToHom _) ≫ _ = _
    rw [eqToHom_map]
    simp only [eqToHom_refl, Category.comp_id] at hn ⊢
    change eqToHom _ ≫ (integralLimitAbComparison l E X).hom = _
    exact hn.symm
  have hi : b.map δ.inv ≫ ac.hom = 𝟙 _ := by
    set_option backward.isDefEq.respectTransparency true in
      exact map_inv_normalized b δ ac.hom hn
  have hd : b.map d.hom ≫ b.map d.inv = 𝟙 _ := (b.mapIso d).hom_inv_id
  have hs : b.map d.hom ≫ b.map δ.inv ≫
      a.hom = b.map (f.map c₀.hom) ≫ b.map (f.map c.hom) ≫
        b.map (f.map k.hom) ≫ chart.inv := by
    set_option backward.isDefEq.respectTransparency true in
      exact normalized_transport (b.map d.hom) (b.map d.inv) (b.map δ.inv) ac.hom
        (b.map (f.map c₀.hom) ≫ b.map (f.map c.hom) ≫
          b.map (f.map k.hom) ≫ chart.inv) hd hi
  let R := continuousMapRingSheaf X (CondensedRing.continuousIntegers l K)
  let A := b.obj R
  let : IsCommMonObj A := by
    set_option backward.isDefEq.respectTransparency true in
      exact Sheaf.isCommMonObj_sheafCompose_obj J R
        (fun U x y ↦ by exact @mul_comm (ULift C(U.unop.left,
          CondensedRing.continuousIntegers l K)) inferInstance x y)
  let H := SheafOfModules.restrictScalars δ.inv ⋙
    SheafOfModules.restrictScalars d.hom
  let G := (CondensedRing.ringModuleEquivalenceOfIso X
      (CondensedRing.reconstructedRingIso X R).symm).functor ⋙
    (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso k)).functor ⋙
    (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c)).functor ⋙
    (CondensedRing.ringModuleEquivalenceOfIso X (f.mapIso c₀)).functor
  let eA := H.mapIso ((CondensedRing.sectionModuleComapIso X a.hom).app M)
  let eB := G.mapIso ((CondensedRing.sectionModuleComapIso X chart.inv).app M)
  let F := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    J (condensedRingObj (CondensedRing.integralCoeff l K) X)).functor
  let W₁ := H.obj ((SheafOfModules.restrictScalars
    (f.map (CondensedRing.sectionRingMap X a.hom))).obj (F.obj M))
  let B₁ := G.obj ((SheafOfModules.restrictScalars
    (f.map (CondensedRing.sectionRingMap X chart.inv))).obj (F.obj M))
  have hc : d.hom ≫ δ.inv ≫ f.map (CondensedRing.sectionRingMap X a.hom) =
      (f.mapIso c₀).hom ≫ (f.mapIso c).hom ≫ (f.mapIso k).hom ≫
        (CondensedRing.reconstructedRingIso X R).inv ≫
          f.map (CondensedRing.sectionRingMap X chart.inv) := by
    have hγ : b.map (f.map (CondensedRing.sectionRingMap X a.hom)) = a.hom :=
      sectionRingMap_underlying X a.hom
    have hε : b.map (f.map (CondensedRing.sectionRingMap X chart.inv)) = chart.inv :=
      sectionRingMap_underlying X chart.inv
    have hρ : b.map (CondensedRing.reconstructedRingIso X R).inv = 𝟙 _ :=
      reconstructedRingIso_underlying X R
    apply b.map_injective
    simp only [b.map_comp, Functor.mapIso_hom, hγ, hε, hρ]
    exact hs
  have ec : W₁ ≅ B₁ := by
    set_option backward.isDefEq.respectTransparency true in
      exact transport_chain_iso X d.hom δ.inv
        (f.map (CondensedRing.sectionRingMap X a.hom))
        (f.mapIso c₀) (f.mapIso c) (f.mapIso k)
        (CondensedRing.reconstructedRingIso X R).symm
        (f.map (CondensedRing.sectionRingMap X chart.inv)) hc (F.obj M)
  have ecomp : W ≅ B := eA ≪≫ ec ≪≫ eB.symm
  have hB := Scheme.fp_iso X (Scheme.pbcIntegralDatum l E) ecomp hmodels
  obtain ⟨S, hS⟩ := hB
  refine ⟨S, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hS i
  apply (localModels_cover_iff_sieve
    (Scheme.ProEt.topology (S.domain i))
    (latticeModuleRing (S.domain i) (latticeCoefficientIntegers l E))
    (fun P : ModuleCat.{u + 1} (ULift.{u + 1} (latticeCoefficientIntegers l E)) ↦
      Module.FinitePresentation _ P)
    (continuousCoefficientModule (S.domain i) (latticeCoefficientIntegers l E))
    (continuousModulePullback (S.immersion i) (latticeCoefficientIntegers l E) Q)).mpr
  exact ⟨V, hV, fun U g hg ↦
    (continuousIntegralSliceModelComparison X l E s c₀ hc₀
      (S.immersion i) Q U).mpr (hv U g hg)⟩

end AlgebraicGeometry.ProEtale
