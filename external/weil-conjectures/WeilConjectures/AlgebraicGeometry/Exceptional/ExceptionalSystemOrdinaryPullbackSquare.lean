/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import all WeilConjectures.AlgebraicGeometry.AdicImmersionModuleNormalization
import all WeilConjectures.AlgebraicGeometry.AdicImmersionCompletedModel
import all WeilConjectures.AlgebraicGeometry.SfbCompletionNormalization
import all WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
import all WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import all WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import all WeilConjectures.ConstructibleSheaf.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import all WeilConjectures.AlgebraicGeometry.RestrictionLocalCompleteness
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.RingTheory.Ideal.Maps
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import all WeilConjectures.CategoryTheory.RingedSiteLocalization
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Sites.LeftExact
import all WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import all WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import all WeilConjectures.CategoryTheory.SliceAwayLocalization
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Exact.Basic
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
import all WeilConjectures.AlgebraicGeometry.RestrictionDerivedProducts
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all WeilConjectures.AlgebraicGeometry.LocalHomTowerCriterion
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all WeilConjectures.Algebra.Homology.LocalCoefficientTelescopeDual
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import all WeilConjectures.CategoryTheory.SequentialTelescopeMono
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import all Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Linear
import all Mathlib.Algebra.Module.ULift
import all WeilConjectures.RingTheory.ModuleLocalizationTowerVanishing
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import all Mathlib.RingTheory.Ideal.Span
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import all Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all WeilConjectures.Algebra.Homology.HomTensorTotal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import all WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import all Mathlib.Algebra.Category.ModuleCat.Colimits
import all Mathlib.Algebra.Module.LocalizedModule.Basic
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all WeilConjectures.RingTheory.TwoLocalizationExact
import all Mathlib.RingTheory.Coprime.Lemmas
import all Mathlib.Tactic.LinearCombination
import all Mathlib.Tactic.Ring
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import all WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.AdicStratumCoverConservativity
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import all Mathlib.CategoryTheory.Sites.LocalProperties
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ExactCompletedKoszulPullback
import all WeilConjectures.AlgebraicGeometry.StrictCompletedKoszulTowerPullback
import all WeilConjectures.AlgebraicGeometry.RingedComplexTensorPullback
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedKoszulDualTowerPullback
import all WeilConjectures.AlgebraicGeometry.FiniteFreeComplexDualPullback
import all WeilConjectures.CategoryTheory.RingedHomPullback.RingedHomComplexPullbackShiftSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomComplexToSingle
import all WeilConjectures.AlgebraicGeometry.RingComplexEndomorphismSelfDual
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.AlgebraicGeometry.CompletedPositiveKoszulPullback
import all Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import all WeilConjectures.AlgebraicGeometry.ConstantPullbackScalar
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantInverseImageSectionSupplement
import all WeilConjectures.CategoryTheory.ConstantRingSectionRigidity
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.Algebra.Polynomial.Roots
import all Mathlib.Algebra.Ring.Hom.InjSurj
import all WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.Basic.Denumerable
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import all WeilConjectures.CategoryTheory.Flat.FlatScalarKoszulTowerComparisonSupplement
import all WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import all WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import all Mathlib.CategoryTheory.Filtered.Final
import all Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import all WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import all WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import all Mathlib.CategoryTheory.Monoidal.Closed.Braided
import all Mathlib.CategoryTheory.Limits.Preserves.Opposites
import all WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
import all WeilConjectures.CategoryTheory.RingedKoszulDualizable
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import all WeilConjectures.Algebra.Homology.Monoidal.Dual
import all WeilConjectures.CategoryTheory.Monoidal.Dualizable
import all WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import all WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import all WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import all Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
import all WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import all WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import all WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
import all WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import all WeilConjectures.Algebra.Homology.TelescopeColimit
import all WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import all WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import all WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import all WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import all Mathlib.CategoryTheory.Limits.Preserves.Finite
import all WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import all Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import all WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import all Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import all Mathlib.CategoryTheory.Sites.RegularEpi
import all Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import all Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.Mathlib.CategoryTheory.NatIso
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import all WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.AffineScheme
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import all WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import all WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import all WeilConjectures.RingTheory.ProEtale.WContractible
import all Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all Mathlib.RingTheory.RingHom.FaithfullyFlat
import all WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.CategoryTheory.Site.SiteAlgebraicCompositionUnitSupplement
import all WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages

/-! # Ordinary normalized system pullback squares -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

section UnderlyingSystems
universe c cv e ev w
variable {A : Type c} [Category.{cv} A] {J : GrothendieckTopology A}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  {B : Type e} [Category.{ev} B] {K : GrothendieckTopology B}
  [EssentiallySmall.{w} A] [EssentiallySmall.{w} B]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  {R : Type w} [CommRing R] {l : R}
  {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
  {V : Sheaf K (Type w) ⥤ Sheaf J (Type w)} {adj : L ⊣ V}

private def setTransition (M : CoefficientSystem (J := J) R l) (n : ℕ) :=
  (coefficientUnderlying (J := J) R l (n + 1)).map (M.transition n) ≫
    (coefficientRestrictionUnderlying (J := J) R l (Nat.le_succ n)).hom.app (M.level n)

private def imageUnderlying (S : CoefficientSystemOrdinaryImage R l L V adj)
    (M : CoefficientSystem (J := J) R l) (n : ℕ) :
    (coefficientUnderlying (J := K) R l n).obj ((S.inverse.obj M).level n) ≅
      L.obj ((coefficientUnderlying (J := J) R l n).obj (M.level n)) :=
  (coefficientUnderlying (J := K) R l n).mapIso ((S.inverseEvaluation n).app M) ≪≫
    (S.lift n).moduleUnderlying.app (M.level n)

private theorem imageUnderlying_transition (S : CoefficientSystemOrdinaryImage R l L V adj)
    (M : CoefficientSystem (J := J) R l) (n : ℕ) :
    setTransition (S.inverse.obj M) n ≫ (imageUnderlying S M n).hom =
      (imageUnderlying S M (n + 1)).hom ≫ L.map (setTransition M n) := by
  exact (transition_bridge (F₀ := (S.lift n).modules) (F₁ := (S.lift (n + 1)).modules)
    (RA := coefficientRestriction (J := J) R l (Nat.le_succ n))
    (RB := coefficientRestriction (J := K) R l (Nat.le_succ n))
    (Ua := coefficientUnderlying (J := J) R l (n + 1))
    (Un := coefficientUnderlying (J := J) R l n)
    (Ub := coefficientUnderlying (J := K) R l (n + 1))
    (Uq := coefficientUnderlying (J := K) R l n)
    (L := L) (ra := coefficientRestrictionUnderlying (J := J) R l (Nat.le_succ n))
    (rb := coefficientRestrictionUnderlying (J := K) R l (Nat.le_succ n))
    (mu₀ := (S.lift n).moduleUnderlying) (mu₁ := (S.lift (n + 1)).moduleUnderlying)
    (β := S.restrictInverse (Nat.le_succ n)) (S.restrictInverseUnderlying (Nat.le_succ n))
    (M.level n) (M.level (n + 1)) ((S.inverse.obj M).level n)
    ((S.inverse.obj M).level (n + 1)) ((S.inverseEvaluation n).hom.app M)
    ((S.inverseEvaluation (n + 1)).hom.app M) ((S.inverse.obj M).transition n)
    (M.transition n)).mp (S.inverseTransition n M)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})] [EssentiallySmall.{w} A] in
private theorem systemMap_comm (M N : CoefficientSystem (J := J) R l)
    (f : ∀ n, M.level n ⟶ N.level n)
    (h : ∀ n,
      (coefficientUnderlying (J := J) R l (n + 1)).map (f (n + 1)) ≫
        setTransition N n = setTransition M n ≫
          (coefficientUnderlying (J := J) R l n).map (f n)) (n : ℕ) :
    f (n + 1) ≫ N.transition n = M.transition n ≫
      (coefficientRestriction (J := J) R l (Nat.le_succ n)).map (f n) := by
  apply (coefficientUnderlying (J := J) R l (n + 1)).map_injective
  apply (cancel_mono ((coefficientRestrictionUnderlying (J := J) R l
    (Nat.le_succ n)).hom.app (N.level n))).1
  simp only [Functor.map_comp, Category.assoc]
  have hr := (coefficientRestrictionUnderlying (J := J) R l
    (Nat.le_succ n)).hom.naturality (f n)
  dsimp only [Functor.comp_map] at hr
  erw [hr]
  simpa only [setTransition, coefficientUnderlying, Functor.comp_map, Category.assoc] using h n

end UnderlyingSystems

private theorem removeUnderlyingLift
    {A B : Type*} [Category A] [Category B]
    (U : A ⥤ A) (V : B ⥤ B) (eU : U ≅ 𝟭 A) (eV : V ≅ 𝟭 B)
    {L L' : A ⥤ B} (γ : L ≅ L') {a : A} {b c : B}
    (α : b ⟶ L.obj a) (β : L'.obj a ⟶ c) (f : b ⟶ c)
    (hf : V.map f = eV.hom.app b ≫ α ≫ L.map (eU.inv.app a) ≫
      γ.hom.app (U.obj a) ≫ L'.map (eU.hom.app a) ≫ β ≫ eV.inv.app c) :
    f = α ≫ γ.hom.app a ≫ β := by
  apply (cancel_epi (eV.hom.app b)).1
  calc
    eV.hom.app b ≫ f = V.map f ≫ eV.hom.app c := (eV.hom.naturality f).symm
    _ = eV.hom.app b ≫ α ≫ γ.hom.app a ≫ β := by
      rw [hf]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      rw [γ.hom.naturality_assoc]
      erw [← L'.map_comp_assoc, Iso.inv_hom_id_app, L'.map_id, Category.id_comp,
        Category.comp_id]

private theorem normalizedDiagonal
    {A B C D E F G H : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category G] [Category H]
    (a : A ⥤ B) (b : B ⥤ D) (c : A ⥤ C) (d : C ⥤ D)
    (Ua : A ⥤ E) (Ub : B ⥤ F) (Uc : C ⥤ G) (Ud : D ⥤ H)
    (p : E ⥤ F) (q : F ⥤ H) (r : E ⥤ G) (s : G ⥤ H)
    (μa : a ⋙ Ub ≅ Ua ⋙ p) (μb : b ⋙ Ud ≅ Ub ⋙ q)
    (μc : c ⋙ Uc ≅ Ua ⋙ r) (μd : d ⋙ Ud ≅ Uc ⋙ s)
    (γ : p ⋙ q ≅ r ⋙ s) (v : a ⋙ b ≅ c ⋙ d)
    (hv : ∀ M, Ud.map (v.hom.app M) ≫ μd.hom.app (c.obj M) ≫
      s.map (μc.hom.app M) = μb.hom.app (a.obj M) ≫
        q.map (μa.hom.app M) ≫ γ.hom.app (Ua.obj M))
    {M : A} {N : B} {N' : C} {K K' : D}
    (ea : N ≅ a.obj M) (eb : K ≅ b.obj N)
    (ec : N' ≅ c.obj M) (ed : K' ≅ d.obj N') :
    Ud.map (eb.hom ≫ b.map ea.hom ≫ v.hom.app M ≫ d.map ec.inv ≫ ed.inv) ≫
      Ud.map ed.hom ≫ μd.hom.app N' ≫ s.map (Uc.map ec.hom) ≫
        s.map (μc.hom.app M) =
      Ud.map eb.hom ≫ μb.hom.app N ≫ q.map (Ub.map ea.hom) ≫
        q.map (μa.hom.app M) ≫ γ.hom.app (Ua.obj M) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Ud.map_comp_assoc ed.inv ed.hom, Iso.inv_hom_id, Ud.map_id,
    Category.id_comp]
  have hd := μd.hom.naturality ec.inv
  dsimp only [Functor.comp_map] at hd
  rw [reassoc_of% hd, ← s.map_comp_assoc, ← Uc.map_comp, Iso.inv_hom_id,
    Uc.map_id, s.map_id, Category.id_comp, hv M]
  have hb := μb.hom.naturality ea.hom
  dsimp only [Functor.comp_map] at hb
  rw [reassoc_of% hb]

variable {O : Type (u + 1)} [CommRing O] {ell : O}

variable {X : Scheme.{u}}

private theorem coefficientRing_ext (n : ℕ)
    (q q' : coefficientQuotientSheaf (J := Scheme.ProEt.topology X) O ell n ⟶
      coefficientQuotientSheaf (J := Scheme.ProEt.topology X) O ell n)
    (h : ∀ x, coefficientConstantSection (J := Scheme.ProEt.topology X) O ell n x ≫
      (sheafCompose _ (forget CommRingCat.{u + 1})).map q =
      coefficientConstantSection (J := Scheme.ProEt.topology X) O ell n x ≫
      (sheafCompose _ (forget CommRingCat.{u + 1})).map q') : q = q' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (coefficientQuotientSheaf
    (J := Scheme.ProEt.topology X) O ell n).property
  ext V x
  have hx := congrArg
    ((sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1))).homEquiv _ _)
    (h x)
  simp only [Adjunction.homEquiv_naturality_right, coefficientConstantSection,
    Equiv.apply_symm_apply] at hx
  exact congrArg (fun t ↦ t.app V PUnit.unit) hx

-- Check the constant generators in an abstract square, before specializing its functors.
private theorem constantSection_comparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (γ : F ⋙ G ≅ H ⋙ I)
    {S R : A} {SB RB : B} {SC RC : C} {SD RD : D}
    (eFS : F.obj S ≅ SB) (eGS : G.obj SB ≅ SD)
    (eHS : H.obj S ≅ SC) (eIS : I.obj SC ≅ SD)
    (eFR : F.obj R ≅ RB) (eGR : G.obj RB ≅ RD)
    (eHR : H.obj R ≅ RC) (eIR : I.obj RC ≅ RD)
    (hs : G.map eFS.hom ≫ eGS.hom = γ.hom.app S ≫ I.map eHS.hom ≫ eIS.hom)
    (s : S ⟶ R) (sB : SB ⟶ RB) (sC : SC ⟶ RC) (sD : SD ⟶ RD)
    (hF : F.map s ≫ eFR.hom = eFS.hom ≫ sB)
    (hG : G.map sB ≫ eGR.hom = eGS.hom ≫ sD)
    (hH : H.map s ≫ eHR.hom = eHS.hom ≫ sC)
    (hI : I.map sC ≫ eIR.hom = eIS.hom ≫ sD) :
    sD ≫ eGR.inv ≫ G.map eFR.inv ≫ γ.hom.app R ≫ I.map eHR.hom ≫ eIR.hom = sD := by
  apply (cancel_epi (G.map eFS.hom ≫ eGS.hom)).1
  have hF' := congrArg (· ≫ eFR.inv) hF
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hF'
  have hG' := congrArg (· ≫ eGR.inv) hG
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hG'
  have hFmap := congrArg G.map hF'.symm
  have hHmap := congrArg I.map hH
  simp only [Functor.map_comp] at hFmap hHmap
  simp only [Category.assoc]
  have hγ := γ.hom.naturality s
  dsimp only [Functor.comp_map] at hγ
  rw [← reassoc_of% hG', reassoc_of% hFmap, reassoc_of% hγ,
    reassoc_of% hHmap, hI, ← reassoc_of% hs]

-- Comparing constant generators unfolds several prescribed geometric inverse-image functors.
private theorem coefficientComparisonRing_id {U : Scheme.{u}} (g : X ⟶ U)
    {PX : StrictEtaleEvaluation X O ell} {PU : StrictEtaleEvaluation U O ell}
    (CX : ExceptionalSystemSiteComparison O ell X PX)
    (CU : ExceptionalSystemSiteComparison O ell U PU)
    (E : StrictEtaleOrdinaryImage O ell g) (P : ExceptionalProOrdinaryImage O ell g)
    (n : ℕ)
    (q : coefficientQuotientSheaf (J := Scheme.ProEt.topology X) O ell n ≅
      coefficientQuotientSheaf (J := Scheme.ProEt.topology X) O ell n)
    (hq : (sheafCompose _ (forget CommRingCat.{u + 1})).map q.hom =
      (P.lift n).ringUnderlying.inv ≫
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1))).map
        (CU.ordinary.lift n).ringUnderlying.inv ≫
      (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) g).inv.app _ ≫
      (ProEtale.comparisonCoefficientPullback (Type (u + 1)) X).map
        (E.lift n).ringUnderlying.hom ≫ (CX.ordinary.lift n).ringUnderlying.hom) :
    q.hom = 𝟙 _ := by
  let L := Scheme.proEtaleSheafInverseImage g (Type (u + 1))
  let C := ProEtale.comparisonCoefficientPullback (Type (u + 1)) X
  let γ : (ProEtale.comparisonCoefficientPullback (Type (u + 1)) U ⋙
      Scheme.proEtaleSheafInverseImage g (Type (u + 1))) ≅
      (Scheme.etaleSetPullback g ⋙
        ProEtale.comparisonCoefficientPullback (Type (u + 1)) X) :=
    (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) g).symm
  have : PreservesFiniteLimits (constantSheaf (Scheme.ProEt.topology X)
      (Type (u + 1))) := by unfold constantSheaf; infer_instance
  have ht : IsTerminal
      ((constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj PUnit) :=
    Types.isTerminalPUnit.isTerminalObj _
  have hsingle : L.map CU.ordinary.singleton.hom ≫ P.singleton.hom =
      γ.hom.app _ ≫ C.map E.singleton.hom ≫ CX.ordinary.singleton.hom := ht.hom_ext _ _
  apply coefficientRing_ext n
  intro x
  rw [hq]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact constantSection_comparison
      (ProEtale.comparisonCoefficientPullback (Type (u + 1)) U) L
      (Scheme.etaleSetPullback g) C γ
      CU.ordinary.singleton P.singleton E.singleton CX.ordinary.singleton
      (CU.ordinary.lift n).ringUnderlying (P.lift n).ringUnderlying
      (E.lift n).ringUnderlying (CX.ordinary.lift n).ringUnderlying hsingle
      (coefficientConstantSection (J := U.smallEtaleTopology) O ell n x)
      (coefficientConstantSection (J := Scheme.ProEt.topology U) O ell n x)
      (coefficientConstantSection (J := X.smallEtaleTopology) O ell n x)
      (coefficientConstantSection (J := Scheme.ProEt.topology X) O ell n x)
      (CU.ordinary.constants n x) (P.constants n x) (E.constants n x)
      (CX.ordinary.constants n x)

-- Transporting the two algebraic presentations requires large sheaf-functor conversions.
private theorem finiteComparison
    {T U : Scheme.{u}} (g : T ⟶ U)
    {PT : StrictEtaleEvaluation T O ell} {PU : StrictEtaleEvaluation U O ell}
    (CT : ExceptionalSystemSiteComparison O ell T PT)
    (CU : ExceptionalSystemSiteComparison O ell U PU)
    (E : StrictEtaleOrdinaryImage O ell g) (P : ExceptionalProOrdinaryImage O ell g)
    (n : ℕ) :
    ∃ level : (CU.ordinary.lift n).modules ⋙ (P.lift n).modules ≅
      (E.lift n).modules ⋙ (CT.ordinary.lift n).modules,
    ∀ M,
    (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n).map
        (level.hom.app M) ≫
      (CT.ordinary.lift n).moduleUnderlying.hom.app ((E.lift n).modules.obj M) ≫
      (ProEtale.comparisonCoefficientPullback (Type (u + 1)) T).map
        ((E.lift n).moduleUnderlying.hom.app M) =
    (P.lift n).moduleUnderlying.hom.app ((CU.ordinary.lift n).modules.obj M) ≫
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1))).map
        ((CU.ordinary.lift n).moduleUnderlying.hom.app M) ≫
      (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) g).inv.app
        ((coefficientUnderlying (J := U.smallEtaleTopology) O ell n).obj M) := by
  have : PreservesFiniteLimits
      (ProEtale.comparisonCoefficientPullback (Type (u + 1)) U) := by
    dsimp [ProEtale.comparisonCoefficientPullback]
    exact Scheme.preservesFiniteLimits_proEtaleSiteComparison U
  have : PreservesFiniteLimits (Scheme.proEtaleSheafInverseImage g (Type (u + 1))) := by
    exact (ProEtale.toposFunctorialityInverseImage g (𝟙 U)).2.2.2.1
  let I := Scheme.SfbImmersionNormalization.compositePresentation
    (CU.ordinary.lift n) (P.lift n)
  let I' := Scheme.SfbImmersionNormalization.compositePresentation
    (E.lift n) (CT.ordinary.lift n)
  let γ : (ProEtale.comparisonCoefficientPullback (Type (u + 1)) U ⋙
      Scheme.proEtaleSheafInverseImage g (Type (u + 1))) ≅
      (Scheme.etaleSetPullback g ⋙
        ProEtale.comparisonCoefficientPullback (Type (u + 1)) T) :=
    (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) g).symm
  let F' := CategoryTheory.GeometricMorphism.inverseImageUniverses.{u + 1, u + 1, u, u + 1, u} I
  let G' := CategoryTheory.GeometricMorphism.inverseImageUniverses.{u + 1, u + 1, u, u + 1, u} I'
  obtain ⟨q, hq, e, he, hs⟩ := CategoryTheory.algebraicComparison γ
    (coefficientQuotientSheaf (J := U.smallEtaleTopology) O ell n)
    (coefficientQuotientSheaf (J := Scheme.ProEt.topology T) O ell n)
    (coefficientQuotientSheaf (J := Scheme.ProEt.topology T) O ell n) F' G'
  have hq' : (sheafCompose _ (forget CommRingCat.{u + 1})).map q.hom =
      I.ringUnderlying.inv ≫ γ.hom.app _ ≫ I'.ringUnderlying.hom := by
    apply removeUnderlyingLift
      (sheafCompose U.smallEtaleTopology uliftFunctor.{u + 1, u + 1})
      (sheafCompose (Scheme.ProEt.topology T) uliftFunctor.{u + 1, u + 1})
      GeometricMorphism.unliftSetSheafIso GeometricMorphism.unliftSetSheafIso γ
    simp only [F', G', GeometricMorphism.inverseImageUniverses,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] at hq
    convert hq using 1 <;> rfl
  have hqid : q.hom = 𝟙 _ := coefficientComparisonRing_id g CT CU E P n q (by
    simpa only [I, I', γ, Iso.symm_hom,
      Scheme.SfbImmersionNormalization.compositePresentation,
      Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Category.assoc, sheafCompose, Functor.comp_obj,
      Functor.comp_map, ProEtale.comparisonCoefficientPullback] using hq')
  let τ : I.modules ⟶ I'.modules :=
    { app M :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := (I.modules.obj M).val.obj V)
                (Y := (I'.modules.obj M).val.obj V)
                { toFun := (e.hom.app M).hom.app V
                  map_add' := ((e.hom.app M).hom.app V).hom.map_add
                  map_smul' := by
                    intro a x
                    have hh := hs M V a x
                    have hqa : q.hom.hom.app V a = a :=
                      congrArg (fun t ↦ t.hom.app V a) hqid
                    simpa only [hqa, RingHom.id_apply, id_eq] using hh }
              naturality := by
                intro V W f
                ext x
                exact congrArg (fun k ↦ k x) ((e.hom.app M).hom.naturality f) } }
      naturality := by
        intro M N f
        ext V x
        exact congrArg (fun k ↦ k.hom.app V x) (e.hom.naturality f) }
  have (M : coefficientLevelModules (J := U.smallEtaleTopology) O ell n) :
      IsIso (τ.app M) := by
    have : IsIso ((SheafOfModules.toSheaf _).map (τ.app M)) := by
      change IsIso (e.hom.app M)
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine ⟨asIso τ, ?_⟩
  intro M
  have he' : (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n).map
      (τ.app M) = I.moduleUnderlying.hom.app M ≫ γ.hom.app _ ≫
        I'.moduleUnderlying.inv.app M := by
    apply removeUnderlyingLift
      (sheafCompose U.smallEtaleTopology uliftFunctor.{u + 1, u + 1})
      (sheafCompose (Scheme.ProEt.topology T) uliftFunctor.{u + 1, u + 1})
      GeometricMorphism.unliftSetSheafIso GeometricMorphism.unliftSetSheafIso γ
    have hM := he M
    simp only [F', G', GeometricMorphism.inverseImageUniverses,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      whiskerLeft_app, whiskerRight_app, NatTrans.comp_app, Category.assoc] at hM
    convert hM using 1 <;> rfl
  have hh : (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n).map
      (τ.app M) ≫ I'.moduleUnderlying.hom.app M =
        I.moduleUnderlying.hom.app M ≫ γ.hom.app _ := by
    apply (Iso.eq_comp_inv (I'.moduleUnderlying.app M)).mp
    exact he'.trans (Category.assoc _ _ _).symm
  simpa only [I, I', γ, Scheme.SfbImmersionNormalization.compositePresentation,
    Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    asIso_hom, Iso.symm_hom] using hh

-- Assembly compares both inverse-image paths at every coefficient level and system transition.
/-- The normalized pullback comparison on ordinary coefficient systems and levels.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03D2, 099R and 0B65.
(blueprint: lem-sf-exceptional-system-ordinary-pullback-square).

Proof: On underlying sheaves use the inverse of the canonical comparison between
etale and pro-etale inverse images. Compose the two algebraic inverse-image
presentations on each path, inserting the canonical equal-universe ULift comparisons
when using the independent-universe algebraic comparison API. Their ring comparison
fixes every constant coefficient by the constants normalization, hence is the identity
by the universal property of constant ring sheafification. The algebraic comparison
on modules is therefore linear over the fixed coefficient quotient. Its underlying
equation is the first
displayed equality and determines it uniquely. Compatibility with restriction of
scalars follows by applying the faithful underlying-sheaf functor and the normalized
restriction comparisons. Assemble these level comparisons into a system comparison,
using the transition normalization of the prescribed system inverse functors. Its
components are isomorphisms, so it is an isomorphism; the construction gives the
second displayed equation. No derived functor or open adjoint is used. -/
theorem exceptionalSystemOrdinaryPullbackSquare_exists
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    {T U : Scheme.{u}} (g : T ⟶ U)
    {PT : StrictEtaleEvaluation T O ell} {PU : StrictEtaleEvaluation U O ell}
    (CT : ExceptionalSystemSiteComparison O ell T PT)
    (CU : ExceptionalSystemSiteComparison O ell U PU)
    (E : StrictEtaleOrdinaryImage O ell g) (P : ExceptionalProOrdinaryImage O ell g) :
    ∃ ordinary : CU.ordinary.inverse ⋙ P.inverse ≅ E.inverse ⋙ CT.ordinary.inverse,
    ∃ level : ∀ n, (CU.ordinary.lift n).modules ⋙ (P.lift n).modules ≅
      (E.lift n).modules ⋙ (CT.ordinary.lift n).modules,
    -- underlying
    (∀ n (M : strictEtaleLevel U O ell n),
    (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n).map
        ((level n).hom.app M) ≫
      (CT.ordinary.lift n).moduleUnderlying.hom.app ((E.lift n).modules.obj M) ≫
      (ProEtale.comparisonCoefficientPullback (Type (u + 1)) T).map
        ((E.lift n).moduleUnderlying.hom.app M) =
    (P.lift n).moduleUnderlying.hom.app ((CU.ordinary.lift n).modules.obj M) ≫
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1))).map
        ((CU.ordinary.lift n).moduleUnderlying.hom.app M) ≫
      (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) g).inv.app
        ((coefficientUnderlying (J := U.smallEtaleTopology) O ell n).obj M)) ∧
    -- ordinaryEvaluation
    (∀ n (M : strictEtaleCoefficientSystem U O ell),
    (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology T) (O := O) (ell :=
      ell) n).map
        (ordinary.hom.app M) ≫
      (CT.ordinary.inverseEvaluation n).hom.app (E.inverse.obj M) ≫
      (CT.ordinary.lift n).modules.map ((E.inverseEvaluation n).hom.app M) =
    (P.inverseEvaluation n).hom.app (CU.ordinary.inverse.obj M) ≫
      (P.lift n).modules.map ((CU.ordinary.inverseEvaluation n).hom.app M) ≫
      (level n).hom.app (M.level n)) := by
  have hf (n : ℕ) := finiteComparison g CT CU E P n
  choose level hu using hf
  let L := Scheme.proEtaleSheafInverseImage g (Type (u + 1))
  let C := ProEtale.comparisonCoefficientPullback (Type (u + 1)) T
  let γ : ProEtale.comparisonCoefficientPullback (Type (u + 1)) U ⋙ L ≅
      Scheme.etaleSetPullback g ⋙ C :=
    (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) g).symm
  let a (n : ℕ) (M : CoefficientSystem (J := U.smallEtaleTopology) O ell) :=
    imageUnderlying P (CU.ordinary.inverse.obj M) n ≪≫
      L.mapIso (imageUnderlying CU.ordinary M n)
  let b (n : ℕ) (M : CoefficientSystem (J := U.smallEtaleTopology) O ell) :=
    imageUnderlying CT.ordinary (E.inverse.obj M) n ≪≫
      C.mapIso (imageUnderlying E M n)
  have ha (M : CoefficientSystem (J := U.smallEtaleTopology) O ell) (n : ℕ) :
      setTransition (P.inverse.obj (CU.ordinary.inverse.obj M)) n ≫ (a n M).hom =
        (a (n + 1) M).hom ≫ L.map
          ((ProEtale.comparisonCoefficientPullback (Type (u + 1)) U).map
            (setTransition M n)) := by
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, imageUnderlying_transition P (CU.ordinary.inverse.obj M) n,
      Category.assoc, ← L.map_comp, imageUnderlying_transition CU.ordinary M n,
      L.map_comp]
    simp only [Category.assoc]
  have hb (M : CoefficientSystem (J := U.smallEtaleTopology) O ell) (n : ℕ) :
      setTransition (CT.ordinary.inverse.obj (E.inverse.obj M)) n ≫ (b n M).hom =
        (b (n + 1) M).hom ≫ C.map
          ((Scheme.etaleSetPullback g).map
            (setTransition M n)) := by
    dsimp only [b, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, imageUnderlying_transition CT.ordinary (E.inverse.obj M) n,
      Category.assoc, ← C.map_comp, imageUnderlying_transition E M n, C.map_comp]
    simp only [Category.assoc]
  let d (n : ℕ) : (CU.ordinary.inverse ⋙ P.inverse) ⋙
      coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T) n ≅
      (E.inverse ⋙ CT.ordinary.inverse) ⋙ coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) n :=
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (P.inverseEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CU.ordinary.inverseEvaluation n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (level n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (E.inverseEvaluation n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (CT.ordinary.inverseEvaluation n).symm ≪≫
    (Functor.associator _ _ _).symm
  have hd (n : ℕ) (M : CoefficientSystem (J := U.smallEtaleTopology) O ell) :
      (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n).map
          ((d n).hom.app M) ≫ (b n M).hom =
        (a n M).hom ≫ γ.hom.app
          ((coefficientUnderlying (J := U.smallEtaleTopology) O ell n).obj (M.level n)) := by
    have hx := normalizedDiagonal
      (CU.ordinary.lift n).modules (P.lift n).modules
      (E.lift n).modules (CT.ordinary.lift n).modules
      (coefficientUnderlying (J := U.smallEtaleTopology) O ell n)
      (coefficientUnderlying (J := Scheme.ProEt.topology U) O ell n)
      (coefficientUnderlying (J := T.smallEtaleTopology) O ell n)
      (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n)
      (ProEtale.comparisonCoefficientPullback (Type (u + 1)) U) L
      (Scheme.etaleSetPullback g) C
      (CU.ordinary.lift n).moduleUnderlying (P.lift n).moduleUnderlying
      (E.lift n).moduleUnderlying (CT.ordinary.lift n).moduleUnderlying
      γ (level n) (hu n) ((CU.ordinary.inverseEvaluation n).app M)
      ((P.inverseEvaluation n).app (CU.ordinary.inverse.obj M))
      ((E.inverseEvaluation n).app M)
      ((CT.ordinary.inverseEvaluation n).app (E.inverse.obj M))
    simpa only [d, a, b, imageUnderlying, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, NatTrans.comp_app, Iso.app_hom, Iso.app_inv,
      Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      Category.assoc, Functor.comp_obj, coefficientEvaluation] using hx
  let τ : CU.ordinary.inverse ⋙ P.inverse ⟶ E.inverse ⋙ CT.ordinary.inverse :=
    { app M :=
        { app := fun n ↦ (d n).hom.app M
          comm := systemMap_comm (P.inverse.obj (CU.ordinary.inverse.obj M))
            (CT.ordinary.inverse.obj (E.inverse.obj M)) (fun n ↦ (d n).hom.app M) (by
            intro n
            apply (cancel_mono (b n M).hom).1
            rw [Category.assoc, hb]
            rw [← Category.assoc, hd, Category.assoc]
            have hn := γ.hom.naturality (setTransition M n)
            dsimp only [Functor.comp_map] at hn
            erw [← hn]
            rw [← Category.assoc, ← ha M n]
            simp only [Category.assoc]
            rw [hd]) }
      naturality := by
        intro M N f
        apply system_hom_ext O ell
        funext n
        exact (d n).hom.naturality f }
  have hτ (M) : IsIso (τ.app M) := by
    refine @JointlyReflectIsomorphisms.isIso _ _ _ _ _ _
      (evaluations_jointlyReflect (K := Scheme.ProEt.topology T) O ell) _ _
      (τ.app M) (fun n ↦ ?_)
    change IsIso ((d n).hom.app M)
    infer_instance
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine ⟨asIso τ, level, hu, ?_⟩
  intro n M
  change (d n).hom.app M ≫
      (CT.ordinary.inverseEvaluation n).hom.app (E.inverse.obj M) ≫
      (CT.ordinary.lift n).modules.map ((E.inverseEvaluation n).hom.app M) =
    (P.inverseEvaluation n).hom.app (CU.ordinary.inverse.obj M) ≫
      (P.lift n).modules.map ((CU.ordinary.inverseEvaluation n).hom.app M) ≫
      (level n).hom.app (M.level n)
  dsimp only [d, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, NatTrans.comp_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end AlgebraicGeometry
