/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Topology.Category.Profinite.AsLimit
import all WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import all WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import all Mathlib.Algebra.Ring.Subring.Basic
import all Mathlib.Algebra.Ring.Pi
import all Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Homeomorph.Lemmas
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.Limits
import all Mathlib.CategoryTheory.FintypeCat
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Limits.Presheaf
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all Mathlib.CategoryTheory.Sites.LocallySurjective
import all Mathlib.CategoryTheory.Monoidal.Mon
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.RingTheory.Ideal.Quotient.PowTransition
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import all Mathlib.RingTheory.Ideal.Maps
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Finiteness.Defs
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Mathlib.CategoryTheory.Limits.Final
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsFlatness
import all WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import all Mathlib.Algebra.Category.ModuleCat.Limits
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.RingTheory.Flat.Basic
import all Mathlib.RingTheory.Flat.Tensor
import all Mathlib.LinearAlgebra.TensorProduct.RightExactness
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Linear.FunctorCategory
import all Mathlib.CategoryTheory.Linear.LinearFunctor
import all WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit
import all Mathlib.CategoryTheory.Limits.Over
import all Mathlib.Algebra.Category.CommAlgCat.Basic
import all WeilConjectures.RingTheory.LimitFlatModules
import all Mathlib.RingTheory.Flat.EquationalCriterion
import all Mathlib.RingTheory.TensorProduct.Quotient
import all Mathlib.RingTheory.Ideal.Quotient.Noetherian
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsProjection
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemModules
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemProperties
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFiniteSystemFlatAndReduction
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionQuotientKernel
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionProjectionKernel
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all Mathlib.CategoryTheory.Adjunction.Restrict
import all Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.CompactAdicContinuousIdentification
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import all Mathlib.Order.Filter.Bases.Basic
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import all Mathlib.Order.CompletePartialOrder
import all WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.ContinuousMap.Compact
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientTerminalSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement

/-! # The coefficient isomorphism for the first residue -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

-- The comparison is made on the point, before pulling coefficients back to a scheme.
private def residueConstants (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶
      Profinite.continuousCoefficientRingPresheaf A where
  app S := RingCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl }
  naturality _ _ _ := rfl

private theorem residueConstants_locallySurjective (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (residueConstants A) where
  imageSieve_mem {S} s := by
    let f : C(S, A) := s.down
    have hclosed (a : A) : IsClosed {x : S | f x = a} :=
      isClosed_singleton.preimage f.continuous
    let (a : A) : CompactSpace {x : S // f x = a} :=
      isCompact_iff_compactSpace.mp (hclosed a).isCompact
    let := Fintype.ofFinite A
    let e := (Fintype.equivFin A).symm
    let U (i : Fin (Fintype.card A)) : Profinite.{u} :=
      Profinite.of {x : S // f x = e i}
    let incl (i : Fin (Fintype.card A)) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨e.symm (f x), ⟨x, (e.apply_symm_apply (f x)).symm⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card A), inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨ULift.up (e i), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private theorem residueConstants_locallyInjective (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (residueConstants A) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext (congrArg
        (fun t : ULift.{u + 1} C(S.unop, A) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

private def residueRingComparison (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IntegralModelsStacks.discreteSheaf A ≅ Profinite.continuousCoefficientRingSheaf A := by
  let J := coherentTopology Profinite.{u}
  let φ := residueConstants A
  let := residueConstants_locallySurjective A
  let := residueConstants_locallyInjective A
  have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map φ) :=
    (J.W_iff φ).mp (J.W_of_isLocallyBijective φ)
  let ψ := ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _
    (Profinite.continuousCoefficientRingSheaf A)).symm φ
  have hψ : ψ = (presheafToSheaf J RingCat.{u + 1}).map φ ≫
      (sheafificationAdjunction J RingCat.{u + 1}).counit.app
        (Profinite.continuousCoefficientRingSheaf A) := rfl
  have : IsIso ψ := by rw [hψ]; infer_instance
  exact (constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
    (CommRingCat.of (ULift.{u + 1} A)) ≪≫ asIso ψ

open IntegralModelsStacks

private abbrev continuousAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (Profinite.continuousMapRingSheafOfUniverse A)

private abbrev constantContinuousMap (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteObj A ⟶ continuousAb A :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (constantToContinuous A)

private instance constantContinuousMap_mon (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : IsMonHom (constantContinuousMap A) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) (constantToContinuous A)

private theorem constantContinuousMap_isIso (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (constantContinuousMap A) := by
  let J := coherentTopology Profinite.{u}
  have hφ : J.W (A := Ab.{u + 1}) (FiniteDiscreteOrdinary.pointConstants A) :=
    J.W_of_isLocallyBijective (FiniteDiscreteOrdinary.pointConstants A)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map
      (FiniteDiscreteOrdinary.pointConstants A)) := (J.W_iff _).mp hφ
  have h : IsIso (FiniteConstantModel.scalarToContinuous A) := by
    change IsIso ((presheafToSheaf J Ab.{u + 1}).map
      (FiniteDiscreteOrdinary.pointConstants A) ≫
        (sheafificationAdjunction J Ab.{u + 1}).counit.app (continuousAb A))
    infer_instance
  have hc := IntegralModelsStacks.pointConstantAbIso_scalar A
  have : IsIso ((IntegralModelsStacks.pointConstantAbIso A).hom ≫
      constantContinuousMap A) := by rw [hc]; exact h
  have heq : constantContinuousMap A =
      (IntegralModelsStacks.pointConstantAbIso A).inv ≫
        FiniteConstantModel.scalarToContinuous A := by
    rw [← hc, Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

private theorem constantContinuousMap_naturality
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    constantContinuousMap A ≫
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (show Profinite.continuousMapRingSheafOfUniverse A ⟶
          Profinite.continuousMapRingSheafOfUniverse B from
          ⟨{ app := fun S ↦ RingCat.ofHom
              (ULift.ringEquiv.symm.toRingHom.comp
                ((f.compLeftContinuous S.unop hf).comp ULift.ringEquiv.toRingHom))
             naturality := fun _ _ _ ↦ rfl }⟩) =
      discreteMap f ≫ constantContinuousMap B := by
  let J := coherentTopology Profinite.{u}
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : J.PreservesSheafification V := GrothendieckTopology.instPreservesSheafification _ _
  let g : CommRingCat.of (ULift.{u + 1} A) ⟶
      CommRingCat.of (ULift.{u + 1} B) := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  have hn := (constantCommuteCompose J V).inv.naturality g
  have hp : (IntegralModelsStacks.pointConstantAbIso A).hom ≫ discreteMap f =
      (constantSheaf J Ab.{u + 1}).map (V.map g) ≫
        (IntegralModelsStacks.pointConstantAbIso B).hom := hn.symm
  apply (cancel_epi (IntegralModelsStacks.pointConstantAbIso A).hom).mp
  rw [← Category.assoc, IntegralModelsStacks.pointConstantAbIso_scalar]
  rw [← Category.assoc, hp]
  rw [Category.assoc, IntegralModelsStacks.pointConstantAbIso_scalar]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (continuousAb B).property
  have hA := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (continuousAb A)).apply_symm_apply (FiniteConstantModel.constantFunctions A)
  have hB := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (continuousAb B)).apply_symm_apply (FiniteConstantModel.constantFunctions B)
  rw [Adjunction.homEquiv_unit] at hA hB
  change toSheafify J _ ≫ (FiniteConstantModel.scalarToContinuous A).hom = _ at hA
  change toSheafify J _ ≫ (FiniteConstantModel.scalarToContinuous B).hom = _ at hB
  change _ ≫ ((FiniteConstantModel.scalarToContinuous A).hom ≫ _) =
    _ ≫ (((constantSheaf J Ab.{u + 1}).map (V.map g)).hom ≫
      (FiniteConstantModel.scalarToContinuous B).hom)
  simp only [← Category.assoc]
  have hn' := toSheafify_naturality J
    ((Functor.const Profinite.{u}ᵒᵖ).map (V.map g))
  change (Functor.const Profinite.{u}ᵒᵖ).map (V.map g) ≫
      toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} B))) =
    toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
        ((constantSheaf J Ab.{u + 1}).map (V.map g)).hom at hn'
  rw [hA]
  erw [← hn']
  rw [Category.assoc, hB]
  ext S a
  rfl

private abbrev coefficientAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] := Profinite.continuousCoefficientRingObj A

private theorem continuousMonEq (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Mon.mk (continuousAb A) = Mon.mk (coefficientAb A) := by
  rfl

private def constantCoefficientMap (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : discreteObj A ⟶ coefficientAb A :=
  constantContinuousMap A ≫ (Mon.forget _).map (eqToHom (continuousMonEq A))

private instance constantCoefficientMap_mon (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : IsMonHom (constantCoefficientMap A) := by
  change IsMonHom (constantContinuousMap A)
  exact constantContinuousMap_mon A

private theorem constantCoefficientMap_isIso (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (constantCoefficientMap A) := by
  let := constantContinuousMap_isIso A
  unfold constantCoefficientMap
  infer_instance

private theorem constantCoefficientMap_naturality
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    constantCoefficientMap A ≫
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (show Profinite.continuousCoefficientRingSheaf A ⟶
          Profinite.continuousCoefficientRingSheaf B from
          ⟨{ app := fun S ↦ RingCat.ofHom
              (ULift.ringEquiv.symm.toRingHom.comp
                ((f.compLeftContinuous S.unop hf).comp ULift.ringEquiv.toRingHom))
             naturality := fun _ _ _ ↦ rfl }⟩) =
      discreteMap f ≫ constantCoefficientMap B := by
  have h := constantContinuousMap_naturality f hf
  convert h using 1 <;> rfl

private theorem constantContinuousMap_topology (A : Type u) [CommRing A]
    (t₁ t₂ : TopologicalSpace A) (ht : t₁ = t₂)
    (h₁ : @IsTopologicalRing A t₁ _) (h₂ : @IsTopologicalRing A t₂ _)
    (he : @continuousAb A _ t₁ h₁ = @coefficientAb A _ t₂ h₂) :
    @constantContinuousMap A _ t₁ h₁ ≫ eqToHom he =
      @constantCoefficientMap A _ t₂ h₂ := by
  subst t₂
  simp only [constantCoefficientMap, eqToHom_map]

private theorem scalarPointMap_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    scalarPointMap l E =
      let := spectralNorm.normedField (Padic l) E
      constantContinuousMap (Padic.coefficientExtensionIntegers l E) := by
  rfl

private theorem mon_eqToIso_inv {C : Type*} [Category C] [MonoidalCategory C]
    {M N : Mon C} (h : M = N) :
    (eqToIso h).inv.hom = eqToHom (congrArg Mon.X h.symm) := by
  subst N
  rfl

private theorem scalarPointMap_absolute (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    scalarPointMap l E ≫ (IntegralConstantModel.pointComparison l E).inv.hom =
      let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
      constantCoefficientMap (Padic.coefficientExtensionIntegers l E) := by
  have ht := DerivedNakayama.coefficientTopology l E
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hpc : (IntegralConstantModel.pointComparison l E).inv.hom =
      eqToHom (congrArg Mon.X (IntegralConstantModel.pointEquality l E).symm) :=
    mon_eqToIso_inv (IntegralConstantModel.pointEquality l E)
  rw [scalarPointMap_eq, hpc]
  exact constantContinuousMap_topology (Padic.coefficientExtensionIntegers l E)
    _ _ hti
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
    (by let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField; infer_instance)
    (congrArg Mon.X (IntegralConstantModel.pointEquality l E).symm)

private def firstResidueIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
      Mon.mk (discreteObj (Padic.coefficientExtensionRing l E 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := DerivedNakayama.quotientDiscrete l E 1
  let := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let := constantCoefficientMap_isIso (Padic.coefficientExtensionRing l E 1)
  exact (Mon.mkIso' (asIso (constantCoefficientMap
    (Padic.coefficientExtensionRing l E 1)))).symm

private theorem firstResidueIso_normalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (scalarPointMap l E ≫ (IntegralConstantModel.pointComparison l E).inv.hom) ≫
      DerivedNakayama.reductionRing l E 1 ≫ (firstResidueIso l E).hom.hom =
        discreteMap (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := DerivedNakayama.quotientDiscrete l E 1
  let := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let := constantCoefficientMap_isIso (Padic.coefficientExtensionRing l E 1)
  rw [scalarPointMap_absolute]
  have h := constantCoefficientMap_naturality
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) continuous_quot_mk
  change constantCoefficientMap _ ≫ DerivedNakayama.reductionRing l E 1 =
    _ ≫ constantCoefficientMap _ at h
  rw [← Category.assoc, h, Category.assoc]
  change _ ≫ (constantCoefficientMap _ ≫ inv (constantCoefficientMap _)) = _
  rw [IsIso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.ProEtale
