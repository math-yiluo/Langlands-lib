/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
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
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.RingTheory.Ideal.Quotient.PowTransition
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all WeilConjectures.CategoryTheory.Flat.FlatRingedIdealCompleteEquivalenceSupplement
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
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
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import all Mathlib.RingTheory.Ideal.Maps
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all Mathlib.CategoryTheory.Sites.Over
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Adjunction.Limits
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
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
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
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
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
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryPullComparison
import all WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackComparisonSupplement
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePullExistence
import all Mathlib.RingTheory.Ideal.Defs
import all WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.QuotientTowerEvaluationComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Constant.ConstantDirectImagePreservesComplete
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.GeometricRingTransport
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Strict quotient towers and the completed-adjunction mate

Source: smooth-purity blueprint, `proposition-composition-base-change-rf-shriek`, Proof Step 4;
Stacks Project, Tags 099M, 099N, 0E48 and 0941
(blueprint: lem-sp-completion-mate-comparison).

## Main definitions and statements

- `towerExchange`: the strict quotient-tower adjunction mate.
- `completeExchange`: the independently defined completed-adjunction mate.
- `projectionComparison`, `comparisonS`, `comparisonT`: the prescribed comparison maps.
- `completionMateComparison`: their natural equality and finite-coefficient formulas.

The auxiliary declarations specify the canonical maps appearing in the statement.
Reduction is a functor to the derived category of strict towers, never a family
of unrelated derived level objects. Every choice below is fixed by a universal
property or a unique representative formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.AdicSites
attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CochainComplex.IsAcyclicTensorKFlat CochainComplex.IsKFlatIndependentCoefficients

attribute [local irreducible] ConstantCompletion.quotientPresentation
  ConstantCompletion.strictLimit ConstantCompletion.derivedExtension ConstantCompletion.derivedPull
  ConstantCompletion.pull

/-- A small site, with its given topology.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
structure Site where
  objects : Type u
  [category : SmallCategory objects]
  topology : GrothendieckTopology objects

attribute [instance] Site.category

/-- The constant coefficient ring sheaf.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.ring (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.constant T.topology A

/-- Module sheaves over the constant coefficient ring, with Mathlib's category.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.modules (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.Mod (T.ring A)

/-- The legacy acyclic-tensor K-flatness is upstream's tensor K-flatness. -/
private theorem Site.isAcyclicTensorKFlat_iff {T : Site.{u}} {A : Type u} [CommRing A]
    (K : CochainComplex (T.modules A) ℤ) : K.IsAcyclicTensorKFlat ↔ K.IsKFlatTensor := by
  unfold CochainComplex.IsAcyclicTensorKFlat
  rfl

/-- Flat-term K-flat resolutions, stated with the legacy K-flatness predicate. -/
private theorem Site.flat_kFlat_resolution (T : Site.{u}) (A : Type u) [CommRing A]
    (X : CochainComplex (T.modules A) ℤ) :
    ∃ (K : CochainComplex (T.modules A) ℤ) (f : K ⟶ X),
      (K.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, (K.X q).IsFlat) ∧ QuasiIso f := by
  obtain ⟨K, f, ⟨hK, hq⟩, hf⟩ :=
    ConstantCompletion.module_flat_kFlat_resolution (J := T.topology) X
  exact ⟨K, f, ⟨(Site.isAcyclicTensorKFlat_iff K).2 hK, hq⟩, hf⟩

/-- Unbounded derived module sheaves, using the standard localization universe.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.derived (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.D (T.ring A)

/-- Strict inverse sequences, indexed by n for the positive exponent n+1.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.towers (T : Site.{u}) (A : Type u) [CommRing A] :=
  ℕᵒᵖ ⥤ T.modules A

/-- Derived category of strict inverse sequences, derived before evaluation.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.towerDerived (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.TD (T.ring A)

/-- The derived quotient tower, with its fixed universal K-flat comparison.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.reduction (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  (ConstantCompletion.quotientPresentation T.topology A I false).tower

/-- Total right derived strict inverse limit, retaining its universal comparison.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.rlim (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.rlim (T.ring A)

/-- Quotient-tower derived completion, not an unspecified reflector.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.completion (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ConstantCompletion.completion T.topology A I false

/-- Its prescribed quotient-tower unit.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.unit (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ConstantCompletion.completionUnit T.topology A I false

/-- Local derived internal-Hom completeness at every section of the constant ideal.
Source: Stacks 0999, 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.IsComplete (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ConstantCompletion.IsComplete (ConstantCompletion.quotient T.topology A I 0)

/-- The full subcategory of locally derived complete objects.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.Complete (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ObjectProperty.FullSubcategory (T.IsComplete A I)

/-- The actual geometric adjunction, with its canonical algebraic inverse-image lift.
The lift records all ring and module operations on generalized sections and the
natural constant-ring identifications; it is not an arbitrary module functor.
Source: Stacks 099N, 00YV, 03D2
(blueprint: lem-sp-completion-mate-comparison). -/
structure Morphism (V U : Site.{u}) where
  inverse : Sheaf V.topology (Type u) ⥤ Sheaf U.topology (Type u)
  direct : Sheaf U.topology (Type u) ⥤ Sheaf V.topology (Type u)
  adjunction : inverse ⊣ direct
  [finiteLimits : PreservesFiniteLimits inverse]
  algebra : ConstantCompletion.InverseImageData inverse

attribute [instance] Morphism.finiteLimits

/-- Constant-coefficient module inverse image, via the canonical constant-ring map.
Source: Stacks 099N, 03D2 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.modulePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : V.modules A ⥤ U.modules A :=
  ConstantCompletion.pull f.algebra (ConstantCompletion.constantMap f.algebra A)

/-- Additivity of the constant-coefficient inverse image, as a named instance.
Source: Stacks 099N, 03D2 (blueprint: lem-sp-completion-mate-comparison).
Proof: unfold the specified inverse image. Scalar extension and ringed inverse image
are additive, so the existing additive-functor instance applies. -/
instance Morphism.modulePull_additive {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : (f.modulePull A).Additive := by
  dsimp only [Morphism.modulePull]
  infer_instance

/-- Exactness and existence of the right adjoint of the specified module inverse image.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison).
Proof: the algebraic lift preserves finite limits and colimits on underlying additive
sheaves. The constant-ring map is an isomorphism, so extension of scalars along it is
an equivalence and exact. Transport the original topos adjunction through the algebraic
operations; the tensor-unit insertion gives the module hom-set bijection. -/
theorem Morphism.modulePull_properties {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    PreservesFiniteLimits (f.modulePull A) ∧ PreservesFiniteColimits (f.modulePull A) ∧
      (f.modulePull A).IsLeftAdjoint := by
  obtain ⟨G, _, adj, _⟩ := ConstantCompletion.module_adjunction_exists
    f.direct f.adjunction f.algebra (ConstantCompletion.constantMap f.algebra A)
  have : IsIso (ConstantCompletion.constantMap f.algebra A) := by
    dsimp only [ConstantCompletion.constantMap]
    infer_instance
  have hlim := ConstantCompletion.pull_finiteLimits_of_isIso f.algebra
    (ConstantCompletion.constantMap f.algebra A)
  have := adj.leftAdjoint_preservesColimits
  exact ⟨hlim, inferInstance, adj.isLeftAdjoint⟩

/-- Finite limits for the exact module inverse image.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePull_finiteLimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteLimits (f.modulePull A) :=
  (f.modulePull_properties A).1

/-- Finite colimits for the exact module inverse image.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePull_finiteColimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteColimits (f.modulePull A) :=
  (f.modulePull_properties A).2.1

/-- The right adjoint is specified by the module hom-functor it represents.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePull_leftAdjoint {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : (f.modulePull A).IsLeftAdjoint :=
  (f.modulePull_properties A).2.2

/-- The module direct image, as the representing right adjoint to the actual inverse image.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.modulePush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : U.modules A ⥤ V.modules A :=
  Functor.rightAdjoint (f.modulePull A)

/-- The fixed module adjunction; all later mates use these same units and counits.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.moduleAdjunction {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : f.modulePull A ⊣ f.modulePush A :=
  Adjunction.ofIsLeftAdjoint (f.modulePull A)

/-- Direct image is additive, as the right adjoint of an additive functor.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePush_additive {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : (f.modulePush A).Additive :=
  (f.moduleAdjunction A).right_adjoint_additive

/-- Standard localization of the actual module category.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Site.hasDerived (T : Site.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory (T.modules A) := HasDerivedCategory.standard _

/-- Standard localization of strict module towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
instance Site.towersHasDerived (T : Site.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory (T.towers A) := HasDerivedCategory.standard _

/-- K-injective resolutions on the small ringed site.
Source: Stacks 079P, 099N (blueprint: lem-sp-completion-mate-comparison).
Proof: module sheaves on a small site form a Grothendieck category, hence have
functorial K-injective resolutions. -/
@[instance]
theorem Site.hasKInjectives (T : Site.{u}) (A : Type u) [CommRing A] :
    Abelian.HasKInjectiveResolutions (T.modules A) := by
  let : IsGrothendieckAbelian.{u} (T.modules A) :=
    SheafOfModules.isGrothendieckAbelian (siteModuleRings (T.ring A))
  infer_instance

/-- K-injective resolutions in strict towers, by their small diagram-site realization.
Source: Stacks 079P, 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: smallModuleDiagrams_isGrothendieckAbelian supplies the Grothendieck property;
apply the K-injective resolution theorem to this abelian category. -/
@[instance]
theorem Site.towersHasKInjectives (T : Site.{u}) (A : Type u) [CommRing A] :
    Abelian.HasKInjectiveResolutions (T.towers A) := by
  let : IsGrothendieckAbelian.{u} (T.towers A) :=
    by
      have := smallModuleDiagrams_isGrothendieckAbelian T.topology
        (siteModuleRings (T.ring A)) (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
      exact IsGrothendieckAbelian.of_equivalence
        (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  infer_instance

/-- Exact inverse image on unbounded derived categories.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.pull {V U : Site.{u}} (f : Morphism V U) (A : Type u) [CommRing A] :=
  (f.modulePull A).mapDerivedCategory

/-- K-injective total right derived module direct image.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.push {V U : Site.{u}} (f : Morphism V U) (A : Type u) [CommRing A] :=
  (f.modulePush A).rightDerivedFunctor

/-- The canonical derived adjunction induced from the fixed ordinary module adjunction.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.adj {V U : Site.{u}} (f : Morphism V U) (A : Type u) [CommRing A] :
    f.pull A ⊣ f.push A :=
  (f.moduleAdjunction A).mapDerivedCategoryRightDerivedAdjunction

/-- Completion has complete output and its quotient unit has the reflection property.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: choose finite generators of I by Noetherianity. Apply
ConstantCompletion.koszul_quotient_reflector to this list. Its unit-preserving
Koszul/quotient comparison gives output completeness and the hom-set bijection;
its last clause identifies the complete inputs. This includes the empty list. -/
theorem Site.completion_properties (T : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    (∀ M : T.derived A, T.IsComplete A I ((T.completion A I).obj M)) ∧
      (∀ (M L : T.derived A), T.IsComplete A I L →
        Function.Bijective (fun a : (T.completion A I).obj M ⟶ L ↦
          (T.unit A I).app M ≫ a)) ∧
      (∀ M : T.derived A, IsIso ((T.unit A I).app M) ↔ T.IsComplete A I M) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  obtain ⟨_, _, h₁, h₂, h₃⟩ :=
    ConstantCompletion.koszul_quotient_reflector T.topology A I false r a ha
  exact ⟨h₁, h₂, h₃⟩

/-- Completion as a functor to the actual full complete subcategory.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def Site.reflector (T : Site.{u}) (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) : T.derived A ⥤ T.Complete A I :=
  ObjectProperty.lift (T.IsComplete A I) (T.completion A I)
    ((T.completion_properties A I).1)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.reflectorAdjunction_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (adj : T.reflector A I ⊣ ObjectProperty.ι (T.IsComplete A I)) : Prop :=
  ∀ (M : T.derived A) (L : T.Complete A I) (a : (T.reflector A I).obj M ⟶ L),
    adj.homEquiv M L a = (T.unit A I).app M ≫ a.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completion adjunction is uniquely fixed by precomposition with its quotient unit.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: the preceding bijection is natural in both arguments by naturality of the
quotient unit. It supplies the adjunction hom equivalence. Surjectivity constructs
its inverse; injectivity proves its inverse identities and uniqueness. -/
theorem Site.reflectorAdjunction_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃! adj : T.reflector A I ⊣ ObjectProperty.ι (T.IsComplete A I),
      Site.reflectorAdjunction_normalized T A I adj := by
  obtain ⟨adj, hadj⟩ := ConstantCompletion.reflector_of_bijective
    (T.IsComplete A I) (T.completion A I) (T.unit A I)
    (T.completion_properties A I).1 (T.completion_properties A I).2.1
  have hn : T.reflectorAdjunction_normalized A I adj := hadj
  refine ⟨adj, hn, ?_⟩
  intro adj' hadj'
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_id,
    hadj' M _ (𝟙 _), hn M _ (𝟙 _)]

/-- The unit-normalized completion adjunction.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def Site.reflectorAdjunction (T : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    T.reflector A I ⊣ ObjectProperty.ι (T.IsComplete A I) :=
  (T.reflectorAdjunction_existsUnique A I).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived direct image preserves local derived completeness.
Source: Stacks 099N(1) (blueprint: lem-sp-completion-mate-comparison).
Proof: apply ConstantCompletion.completedPullbackAdjunction to the given geometric
adjunction. The generalized-section operation identities identify its algebraic lift
with f.algebra. The module hom-set normalization and universal derived comparison
identify its direct image with f.push A; transport its completeness-preservation
clause across that canonical isomorphism. Equivalently, on each slice, adjunction
and localization identify internal Hom from A[1/a] into Rf_*L with direct image
of the corresponding internal Hom into L, which vanishes for complete L. -/
theorem Morphism.push_complete {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (L : U.derived A) (hL : U.IsComplete A I L) :
    V.IsComplete A I ((f.push A).obj L) := by
  let G := f.modulePush A
  let η : G.mapHomologicalComplex (.up ℤ) ⋙ ConstantCompletion.Q (V.ring A) ⟶
      ConstantCompletion.Q (U.ring A) ⋙ f.push A :=
    { app := fun P ↦ G.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
      naturality := fun P Q a ↦ G.rightDerivedFunctorUnit.naturality
        ((HomotopyCategory.quotient _ (.up ℤ)).map a) }
  have hi (P : CochainComplex (U.modules A) ℤ) (hP : P.IsKInjective) :
      IsIso (η.app P) := by
    have := hP
    change IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
    infer_instance
  have hu : (f.push A).IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (U.modules A) (.up ℤ)) := by
    apply (derives G).isRightDerivedFunctor_of_isIso η
    intro P
    exact hi P.obj P.property
  exact ConstantCompletion.constantDirectImage_preservesComplete V.topology U.topology
    A I f.direct f.adjunction f.algebra (AdditiveFunctor.of G) (f.moduleAdjunction A)
    (f.push A) η hu hi L hL

/-- Direct image restricted to the full complete subcategories.
Source: Stacks 099N(1) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completePush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    U.Complete A I ⥤ V.Complete A I :=
  ObjectProperty.lift (V.IsComplete A I)
    (ObjectProperty.ι (U.IsComplete A I) ⋙ f.push A)
    (fun L ↦ f.push_complete A I L.obj L.property)

/-- Completed inverse image is ordinary inverse image followed by the specified reflector.
Source: Stacks 099N(2) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    V.Complete A I ⥤ U.Complete A I :=
  ObjectProperty.ι (V.IsComplete A I) ⋙ f.pull A ⋙ U.reflector A I

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completeAdjunction_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (adj : f.completePull A I ⊣ f.completePush A I) : Prop :=
  ∀ (M : V.Complete A I) (L : U.Complete A I)
    (a : (f.completePull A I).obj M ⟶ L),
    (adj.homEquiv M L a).hom = (f.adj A).homEquiv M.obj L.obj
      ((U.unit A I).app ((f.pull A).obj M.obj) ≫ a.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed adjunction, with exactly the composite ordinary and completion hom bijections.
Source: Stacks 099N(2) (blueprint: lem-sp-completion-mate-comparison).
Proof: transpose a map from C_U f^*M to L first under the completion adjunction,
then under f^* ⊣ Rf_*. Completeness of Rf_*L lets the result be regarded as a
map in the full complete subcategory. The two inverse identities and naturality
follow from those of the two hom bijections. This also proves uniqueness. -/
theorem Morphism.completeAdjunction_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃! adj : f.completePull A I ⊣ f.completePush A I,
      Morphism.completeAdjunction_normalized f A I adj := by
  obtain ⟨adj, hadj⟩ := ConstantCompletion.complete_adjunction
    (V.IsComplete A I) (U.IsComplete A I) (f.pull A) (f.push A) (f.adj A)
    (U.completion A I) (U.unit A I) (U.completion_properties A I).1
    (f.push_complete A I) (U.reflectorAdjunction A I)
    (U.reflectorAdjunction_existsUnique A I).exists.choose_spec
  have hn : f.completeAdjunction_normalized A I adj := fun M L a ↦ hadj M L a.hom
  refine ⟨adj, hn, ?_⟩
  intro adj' hadj'
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply ObjectProperty.hom_ext
  rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_id]
  exact (hadj' M _ (𝟙 _)).trans (hn M _ (𝟙 _)).symm

/-- The completed adjunction with the prescribed hom-set normalization.
Source: Stacks 099N(2) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completeAdjunction {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    f.completePull A I ⊣ f.completePush A I :=
  (f.completeAdjunction_existsUnique A I).exists.choose

variable {Y X Y' X' : Site.{u}}

/-- Termwise inverse image on the strict sequence category.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerModulePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : V.towers A ⥤ U.towers A :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (f.modulePull A)

/-- Termwise direct image before derivation.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerModulePush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : U.towers A ⥤ V.towers A :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (f.modulePush A)

/-- Termwise inverse image is exact, because kernels and cokernels are levelwise.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: evaluate a finite limiting or colimiting cone at each index. Exactness of
modulePull makes the image cone limiting or colimiting at every index, hence in
the functor category. -/
theorem Morphism.towerModulePull_exact {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    PreservesFiniteLimits (f.towerModulePull A) ∧
      PreservesFiniteColimits (f.towerModulePull A) := by
  constructor
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Finite limits of the termwise inverse image.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.towerModulePull_finiteLimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteLimits (f.towerModulePull A) :=
  (f.towerModulePull_exact A).1

/-- Finite colimits of the termwise inverse image.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.towerModulePull_finiteColimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteColimits (f.towerModulePull A) :=
  (f.towerModulePull_exact A).2

/-- Exact derived inverse image of strict towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerPull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] := (f.towerModulePull A).mapDerivedCategory

/-- The total right derived functor of termwise module direct image.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerPush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] := (f.towerModulePush A).rightDerivedFunctor

/-- The derived termwise adjunction, from the same ordinary module adjunction.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.towerAdjunction {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : f.towerPull A ⊣ f.towerPush A :=
  (Adjunction.whiskerRight ℕᵒᵖ (f.moduleAdjunction A)).mapDerivedCategoryRightDerivedAdjunction

/-- A specified commutation isomorphism of the original geometric inverse images.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Square (f : Morphism Y X) (g : Morphism Y Y')
    (h : Morphism X X') (k : Morphism Y' X') :=
  g.inverse ⋙ k.inverse ≅ f.inverse ⋙ h.inverse

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def moduleSquare_normalized
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A]
    (e : g.modulePull A ⋙ k.modulePull A ≅ f.modulePull A ⋙ h.modulePull A) : Prop :=
  ∀ M : Y.modules A,
    k.inverse.map (ConstantCompletion.pullInsertion g.algebra
        (ConstantCompletion.constantMap g.algebra A) M) ≫
      ConstantCompletion.pullInsertion k.algebra
        (ConstantCompletion.constantMap k.algebra A) ((g.modulePull A).obj M) ≫
      (ConstantCompletion.underlying (X'.ring A)).map (e.hom.app M) =
    sq.hom.app ((ConstantCompletion.underlying (Y.ring A)).obj M) ≫
      h.inverse.map (ConstantCompletion.pullInsertion f.algebra
        (ConstantCompletion.constantMap f.algebra A) M) ≫
      ConstantCompletion.pullInsertion h.algebra
        (ConstantCompletion.constantMap h.algebra A) ((f.modulePull A).obj M)

/-- The canonical module square is uniquely fixed on scalar insertions.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison).
Proof: apply the given set-sheaf square to inverse-image modules. Naturality on
generalized sections makes it additive and compatible with the constant A-action.
Extension of scalars sends a generator to its image tensored with 1. These generators
locally generate, so the insertion formula gives uniqueness. Apply the inverse square
to get the inverse map. -/
theorem moduleSquare_existsUnique
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    ∃! e : g.modulePull A ⋙ k.modulePull A ≅ f.modulePull A ⋙ h.modulePull A,
      moduleSquare_normalized sq A e := by
  sorry

/-- The ordinary module comparison with its scalar-insertion normalization.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def moduleSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :=
  (moduleSquare_existsUnique sq A).exists.choose

/-- The ordinary derived square, obtained by exact localization of that module square.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def derivedSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.pull A ⋙ k.pull A ≅ f.pull A ⋙ h.pull A :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (moduleSquare sq A) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The strict module square is the pointwise extension of the original module square.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def towerModuleSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.towerModulePull A ⋙ k.towerModulePull A ≅
      f.towerModulePull A ⋙ h.towerModulePull A :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun n ↦ (moduleSquare sq A).app (M.obj n))
      (fun i ↦ (moduleSquare sq A).hom.naturality (M.map i)))
    (fun a ↦ by
      apply NatTrans.ext
      funext n
      exact (moduleSquare sq A).hom.naturality (a.app n))

/-- The canonical square on derived strict towers.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def towerSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.towerPull A ⋙ k.towerPull A ≅ f.towerPull A ⋙ h.towerPull A :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (towerModuleSquare sq A) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The strict tower exchange, using Mathlib's mate equivalence.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def towerExchange {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    f.towerPush A ⋙ g.towerPull A ⟶ h.towerPull A ⋙ k.towerPush A :=
  (mateEquiv (f.towerAdjunction A) (k.towerAdjunction A)
    (TwoSquare.mk _ _ _ _ (towerSquare sq A).hom))

/-- The ordinary coefficient exchange for any commutative coefficient ring.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def ordinaryExchange {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    f.push A ⋙ g.pull A ⟶ h.pull A ⋙ k.push A :=
  (mateEquiv (f.adj A) (k.adj A)
    (TwoSquare.mk _ _ _ _ (derivedSquare sq A).hom))

/-- The right-adjoint square is the adjunction conjugate of the canonical left square.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def rightSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    h.push A ⋙ f.push A ≅ k.push A ⋙ g.push A :=
  conjugateIsoEquiv ((f.adj A).comp (h.adj A)) ((g.adj A).comp (k.adj A))
    (derivedSquare sq A)

/-- Restrict the same right-adjoint square to complete objects, with no new normalization.
Source: Stacks 099N, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def completeRightSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    h.completePush A I ⋙ f.completePush A I ≅
      k.completePush A I ⋙ g.completePush A I :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((rightSquare sq A).app M.obj))
    (fun a ↦ by ext; exact (rightSquare sq A).hom.naturality a.hom)

/-- The completed pullback square is precisely the conjugate of the prescribed
right-adjoint square through the two composite completed adjunctions.
Source: Stacks 099N, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def completeSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    g.completePull A I ⋙ k.completePull A I ≅
      f.completePull A I ⋙ h.completePull A I :=
  (conjugateIsoEquiv
    ((f.completeAdjunction A I).comp (h.completeAdjunction A I))
    ((g.completeAdjunction A I).comp (k.completeAdjunction A I))).symm
      (completeRightSquare sq A I)

/-- The exchange defined by the completed adjunctions, not by taking a tower limit.
Source: Stacks 099N, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def completeExchange {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    f.completePush A I ⋙ g.completePull A I ⟶
      h.completePull A I ⋙ k.completePush A I :=
  (mateEquiv (f.completeAdjunction A I) (k.completeAdjunction A I)
    (TwoSquare.mk _ _ _ _ (completeSquare sq A I).hom))

/-- Exact derived constant towers, used only to normalize the strict-limit adjunction.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.delta (T : Site.{u}) (A : Type u) [CommRing A] :=
  (ConstantCompletion.constantTower T.topology (T.ring A)).mapDerivedCategory

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.deltaAdjunction_normalized (T : Site.{u}) (A : Type u) [CommRing A]
    (adj : T.delta A ⊣ T.rlim A) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ,
    adj.unit.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
        (T.rlim A).map ((ConstantCompletion.constantTower T.topology
          (T.ring A)).mapDerivedCategoryFactors.hom.app P) =
      (ConstantCompletion.Q (T.ring A)).map
        ((NatTrans.mapHomologicalComplex
          (constLimAdj : ConstantCompletion.constantTower T.topology (T.ring A) ⊣
            (lim : T.towers A ⥤ T.modules A)).unit (.up ℤ)).app P) ≫
      (ConstantCompletion.limitComparison (T.ring A)).app
        (((ConstantCompletion.constantTower T.topology (T.ring A)).mapHomologicalComplex
          (.up ℤ)).obj P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_left_derived_adjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (RF : DerivedCategory D ⥤ DerivedCategory C)
    (β : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomologicalComplex.quasiIso D (.up ℤ))]
    (hβ : ∀ (X : CochainComplex D ℤ), X.IsKInjective → IsIso (β.app X)) :
    ∃! ad : L.mapDerivedCategory ⊣ RF, ∀ X : CochainComplex C ℤ,
      ad.unit.app (DerivedCategory.Q.obj X) ≫
          RF.map (L.mapDerivedCategoryFactors.hom.app X) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app X) ≫
          β.app ((L.mapHomologicalComplex (.up ℤ)).obj X) := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let W' := HomologicalComplex.quasiIso D (.up ℤ)
  let α := L.mapDerivedCategoryFactors.hom
  have : L.mapDerivedCategory.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ L.mapDerivedCategoryFactors
  have : (L.mapDerivedCategory ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α RF) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight L.mapDerivedCategoryFactors RF)
  have : (RF ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight β L.mapDerivedCategory ≫ (Functor.associator _ _ _).hom) W' :=
    (CochainComplex.KInjectives.localizerMorphism D
      ).isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
      (fun X ↦ hβ X.obj X.property) L.mapDerivedCategory
  let ad := (a.mapHomologicalComplex (.up ℤ)).derived W W' α β
  have hn := (a.mapHomologicalComplex (.up ℤ)).derivedη_fac_app W α β
  refine ⟨ad, hn, ?_⟩
  intro ad' hn'
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q W
  intro X
  apply (cancel_mono (RF.map (L.mapDerivedCategoryFactors.hom.app X))).1
  exact (hn' X).trans (hn X).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constant/derived-limit adjunction has the unit computed by the actual
ordinary limit unit and the specified right-derived comparison on every complex.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: derive the exact constant-tower/limit adjunction. The universal right-derived
property identifies its right adjoint with ConstantCompletion.rlim. Transport the
adjunction through that unique comparison. The displayed unit equation is the
derived-adjunction fraction formula and fixes its hom equivalence uniquely. -/
theorem Site.deltaAdjunction_existsUnique (T : Site.{u}) (A : Type u) [CommRing A] :
    ∃! adj : T.delta A ⊣ T.rlim A,
      Site.deltaAdjunction_normalized T A adj := by
  let : Abelian (T.modules A) :=
    { (inferInstance : Abelian (T.modules A)) with
      toPreadditive := (inferInstance : Preadditive (T.modules A)) }
  let : Abelian (T.towers A) :=
    { (inferInstance : Abelian (T.towers A)) with
      toPreadditive := (inferInstance : Preadditive (T.towers A)) }
  have := T.towersHasKInjectives A
  let L := ConstantCompletion.constantTower T.topology (T.ring A)
  let R := (lim : T.towers A ⥤ T.modules A)
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  have : (T.rlim A).IsRightDerivedFunctor (ConstantCompletion.limitComparison (T.ring A))
      (HomologicalComplex.quasiIso (T.towers A) (.up ℤ)) :=
    (ConstantCompletion.strictLimit (T.ring A)).universal
  exact exact_left_derived_adjunction L R constLimAdj (T.rlim A)
    (ConstantCompletion.limitComparison (T.ring A))
    (ConstantCompletion.strictLimit (T.ring A)).computation

/-- The fixed constant-tower/derived-limit adjunction.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Site.deltaAdjunction (T : Site.{u}) (A : Type u) [CommRing A] :=
  (T.deltaAdjunction_existsUnique A).exists.choose

/-- Constant towers commute with termwise inverse image by identity components.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.constantModulePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    ConstantCompletion.constantTower V.topology (V.ring A) ⋙ f.towerModulePull A ≅
      f.modulePull A ⋙ ConstantCompletion.constantTower U.topology (U.ring A) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ by simp)) (fun _ ↦ by ext n; simp)

/-- Its canonical exact derived counterpart.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.constantPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    V.delta A ⋙ f.towerPull A ≅ f.pull A ⋙ U.delta A :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (f.constantModulePullIso A) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The canonical direct-image/derived-limit comparison. It is the adjunction
conjugate of the identity-component constant/inverse-image comparison.
Thus its K-injective computation is the ordinary identity u_* lim = lim u_*.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.directLimitIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    U.rlim A ⋙ f.push A ≅ f.towerPush A ⋙ V.rlim A :=
  conjugateIsoEquiv ((f.adj A).comp (U.deltaAdjunction A))
    ((V.deltaAdjunction A).comp (f.towerAdjunction A)) (f.constantPullIso A)

/-- The finite quotient ring and its original coefficient action.
Source: smooth-purity blueprint, proposition-composition-base-change-rf-shriek Step 4
(blueprint: lem-sp-completion-mate-comparison). -/
abbrev quotientRing (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :=
  A ⧸ I ^ (n + 1)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteModuleRestrictionPullIso_normalized {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n) ⋙
        f.modulePull A ≅ f.modulePull (quotientRing A I n) ⋙
          ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n)) : Prop :=
  ∀ M : V.modules (quotientRing A I n),
    ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
        ((ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n)).obj M) ≫
      (ConstantCompletion.underlying (U.ring A)).map (e.hom.app M) =
    ConstantCompletion.pullInsertion f.algebra
      (ConstantCompletion.constantMap f.algebra (quotientRing A I n)) M

section

attribute [local semireducible] ConstantCompletion.pull

-- Scalar insertion along a ring isomorphism is the unit of an equivalence.
private theorem scalarInsertion_isIso (U : Site.{u})
    {R S : Sheaf U.topology CommRingCat.{u}} (t : R ⟶ S) [IsIso t]
    (M : ConstantCompletion.Mod R) : IsIso (ConstantCompletion.insertion t M) := by
  have : (ConstantCompletion.res t).IsEquivalence :=
    ConstantCompletion.restrictScalars_equivalence
      ((sheafCompose U.topology (forget₂ CommRingCat RingCat)).mapIso (asIso t))
  have := (ConstantCompletion.scalarAdj t).isEquivalence_left_of_isEquivalence_right
  have := (ConstantCompletion.scalarAdj t).unit_isIso_of_L_fully_faithful
  rw [ConstantCompletion.insertion_eq_unit]
  infer_instance

private theorem restrictionPullAdjunct_exists {V U : Site.{u}} (f : Morphism V U)
    {R S : Sheaf V.topology CommRingCat.{u}} {R' S' : Sheaf U.topology CommRingCat.{u}}
    (a : R ⟶ S) (b : R' ⟶ S')
    (c : f.algebra.rings.obj R ⟶ R') (d : f.algebra.rings.obj S ⟶ S')
    (hs : f.algebra.rings.map a ≫ d = c ≫ b) :
    ∃ q₀ : ConstantCompletion.res a ⋙ (f.algebra.algebra R).modules ⟶
        ConstantCompletion.pull f.algebra d ⋙
          ConstantCompletion.res b ⋙ ConstantCompletion.res c,
      ∀ M : ConstantCompletion.Mod S,
        (ConstantCompletion.underlying (f.algebra.rings.obj R)).map (q₀.app M) =
          (f.algebra.algebra R).moduleUnderlying.hom.app
              ((ConstantCompletion.res a).obj M) ≫
            ConstantCompletion.pullInsertion f.algebra d M := by
  let F := f.algebra
  let q₀ := ConstantCompletion.inverseRestriction F a ≫
    Functor.whiskerLeft (F.algebra _).modules
      (Functor.whiskerRight (ConstantCompletion.scalarAdj d).unit
        (ConstantCompletion.res (F.rings.map a))) ≫
    Functor.whiskerLeft (ConstantCompletion.pull F d)
      (ConstantCompletion.squareRestriction (F.rings.map a) d c b hs.symm).hom
  refine ⟨q₀, ?_⟩
  intro M
  ext W x
  dsimp only [q₀, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  change ((ConstantCompletion.squareRestriction (F.rings.map a) d c b hs.symm).hom.app
    _).val.app W _ = _
  rw [ConstantCompletion.squareRestriction_apply]
  rw [ConstantCompletion.pullInsertion, ConstantCompletion.insertion_eq_unit]
  rfl

-- Prove the scalar-restriction comparison over an abstract coefficient square.
-- This keeps quotient-ring constructions out of the normalization argument.
private theorem restrictionPullIso_existsUnique {V U : Site.{u}} (f : Morphism V U)
    {R S : Sheaf V.topology CommRingCat.{u}} {R' S' : Sheaf U.topology CommRingCat.{u}}
    (a : R ⟶ S) (b : R' ⟶ S')
    (c : f.algebra.rings.obj R ⟶ R') (d : f.algebra.rings.obj S ⟶ S')
    [IsIso c] [IsIso d] (hs : f.algebra.rings.map a ≫ d = c ≫ b) :
    ∃! e : ConstantCompletion.res a ⋙ ConstantCompletion.pull f.algebra c ≅
        ConstantCompletion.pull f.algebra d ⋙ ConstantCompletion.res b,
      ∀ M : ConstantCompletion.Mod S,
        ConstantCompletion.pullInsertion f.algebra c ((ConstantCompletion.res a).obj M) ≫
          (ConstantCompletion.underlying R').map (e.hom.app M) =
        ConstantCompletion.pullInsertion f.algebra d M := by
  let F := f.algebra
  obtain ⟨q₀, hq₀⟩ := restrictionPullAdjunct_exists f a b c d hs
  let q : ConstantCompletion.res a ⋙ ConstantCompletion.pull F c ⟶
      ConstantCompletion.pull F d ⋙ ConstantCompletion.res b :=
    { app := fun M ↦ ((ConstantCompletion.scalarAdj c).homEquiv _ _).symm (q₀.app M)
      naturality := by
        intro M N t
        apply ((ConstantCompletion.scalarAdj c).homEquiv _ _).injective
        dsimp only [Functor.comp_map, ConstantCompletion.pull]
        rw [(ConstantCompletion.scalarAdj c).homEquiv_naturality_left,
          (ConstantCompletion.scalarAdj c).homEquiv_naturality_right,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact q₀.naturality t }
  have hn (M : ConstantCompletion.Mod S) :
      ConstantCompletion.pullInsertion F c ((ConstantCompletion.res a).obj M) ≫
        (ConstantCompletion.underlying R').map (q.app M) =
      ConstantCompletion.pullInsertion F d M := by
    rw [← ConstantCompletion.pull_homEquiv]
    change (F.algebra _).moduleUnderlying.inv.app _ ≫
      (ConstantCompletion.underlying _).map
        (((ConstantCompletion.scalarAdj c).homEquiv _ _)
          (((ConstantCompletion.scalarAdj c).homEquiv _ _).symm (q₀.app M))) = _
    rw [Equiv.apply_symm_apply]
    rw [hq₀]
    simp only [F, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hp {R : Sheaf V.topology CommRingCat.{u}}
      {S : Sheaf U.topology CommRingCat.{u}} (t : F.rings.obj R ⟶ S) [IsIso t]
      (M : ConstantCompletion.Mod R) : IsIso (ConstantCompletion.pullInsertion F t M) := by
    have := scalarInsertion_isIso U t ((F.algebra R).modules.obj M)
    dsimp only [ConstantCompletion.pullInsertion]
    infer_instance
  clear_value q
  have hqi (M : ConstantCompletion.Mod S) : IsIso (q.app M) := by
    have := hp c ((ConstantCompletion.res a).obj M)
    have := hp d M
    have hi : IsIso ((ConstantCompletion.underlying R').map (q.app M)) := by
      apply (isIso_comp_left_iff (ConstantCompletion.pullInsertion F c _) _).mp
      rw [hn]
      infer_instance
    exact isIso_of_reflects_iso _ (ConstantCompletion.underlying R')
  have : IsIso q := NatIso.isIso_of_isIso_app q
  refine ⟨asIso q, hn, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have := hp c ((ConstantCompletion.res a).obj M)
  apply (ConstantCompletion.underlying R').map_injective
  apply (cancel_epi (ConstantCompletion.pullInsertion F c
    ((ConstantCompletion.res a).obj M))).mp
  exact (he M).trans (hn M).symm

/-- Ordinary inverse image commutes with finite scalar restriction, fixing its map
on every inverse-image generator, not merely its objects.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison).
Proof: both sides have the same underlying inverse-image additive sheaf and the
same restricted constant A-action. The map is identity on its generalized sections.
Its inverse is the same identity. The displayed insertion formula fixes it uniquely. -/
theorem Morphism.finiteModuleRestrictionPullIso_existsUnique {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n) ⋙
        f.modulePull A ≅ f.modulePull (quotientRing A I n) ⋙
          ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n),
      Morphism.finiteModuleRestrictionPullIso_normalized f A I n e := by
  have : IsIso (ConstantCompletion.constantMap f.algebra A) := by
    dsimp only [ConstantCompletion.constantMap]
    infer_instance
  have : IsIso (ConstantCompletion.constantMap f.algebra (quotientRing A I n)) := by
    dsimp only [ConstantCompletion.constantMap]
    infer_instance
  exact restrictionPullIso_existsUnique f
    (ConstantCompletion.quotient V.topology A I n)
    (ConstantCompletion.quotient U.topology A I n)
    (ConstantCompletion.constantMap f.algebra A)
    (ConstantCompletion.constantMap f.algebra (quotientRing A I n))
    (f.algebra.constants.hom.naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))

end

/-- The normalized ordinary inverse-image/scalar-restriction comparison.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteModuleRestrictionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :=
  (f.finiteModuleRestrictionPullIso_existsUnique A I n).exists.choose

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.moduleReductionPullIso_normalized {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A)
    (e : ConstantCompletion.reductionTower V.topology A I false ⋙ f.towerModulePull A ≅
        f.modulePull A ⋙ ConstantCompletion.reductionTower U.topology A I false) : Prop :=
  ∀ (M : V.modules A) (n : ℕ),
    f.inverse.map (ConstantCompletion.insertion
        (ConstantCompletion.quotient V.topology A I n) M) ≫
      ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
        ((ConstantCompletion.reduction V.topology A I false n).obj M) ≫
      (ConstantCompletion.underlying (U.ring A)).map ((e.hom.app M).app (op n)) =
    ConstantCompletion.pullInsertion f.algebra
        (ConstantCompletion.constantMap f.algebra A) M ≫
      ConstantCompletion.insertion (ConstantCompletion.quotient U.topology A I n)
        ((f.modulePull A).obj M)

section
attribute [local semireducible] ConstantCompletion.pull

private theorem quotientUnit_epi (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (M : T.modules A) :
    Epi ((ConstantCompletion.scalarAdj (ConstantCompletion.quotient T.topology A I n)).unit.app
      M) := by
  let q := ConstantCompletion.quotient T.topology A I n
  constructor
  intro N a b h
  apply ConstantCompletion.restrictedTensor_hom_ext q M N
  intro U t m
  obtain ⟨r, hr⟩ := ConstantCompletion.constantRing_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
    Ideal.Quotient.mk_surjective T.topology U t
  change (q.hom.app U) r = t at hr
  let η := (ConstantCompletion.scalarAdj q).unit.app M
  have ht : η.val.app U (r • m) = ConstantCompletion.tensorSection q M U t m := by
    rw [← hr, ConstantCompletion.tensorSection_smul]
    exact (η.val.app U).hom.map_smul r m
  rw [← ht]
  exact congrArg (fun z ↦ z.val.app U (r • m)) h

private theorem pullInsertion_naturality {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] {M N : V.modules A} (a : M ⟶ N) :
    f.inverse.map ((ConstantCompletion.underlying (V.ring A)).map a) ≫
        ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A) N =
      ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A) M ≫
        (ConstantCompletion.underlying (U.ring A)).map ((f.modulePull A).map a) := by
  symm
  dsimp only [ConstantCompletion.pullInsertion, ConstantCompletion.pull, Functor.comp_map]
  erw [Category.assoc, ConstantCompletion.finiteInsertion_naturality U.topology
    (ConstantCompletion.constantMap f.algebra A), ← Category.assoc,
    ← (f.algebra.algebra _).moduleUnderlying.inv.naturality a, Category.assoc]

private theorem constantPullInsertion_isIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (M : V.modules A) :
    IsIso (ConstantCompletion.pullInsertion f.algebra
      (ConstantCompletion.constantMap f.algebra A) M) := by
  have : IsIso (ConstantCompletion.constantMap f.algebra A) := by
    dsimp only [ConstantCompletion.constantMap]
    infer_instance
  have : (ConstantCompletion.res (ConstantCompletion.constantMap f.algebra A)).IsEquivalence :=
    ConstantCompletion.restrictScalars_equivalence
      ((sheafCompose U.topology (forget₂ CommRingCat RingCat)).mapIso
        (asIso (ConstantCompletion.constantMap f.algebra A)))
  have : IsIso (ConstantCompletion.insertion (ConstantCompletion.constantMap f.algebra A)
      ((f.algebra.algebra _).modules.obj M)) := by
    rw [ConstantCompletion.insertion_eq_unit]
    infer_instance
  dsimp only [ConstantCompletion.pullInsertion]
  infer_instance

private theorem reductionPull_hom_ext {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (M : V.modules A)
    (N : U.modules A)
    (a b : (f.modulePull A).obj ((ConstantCompletion.reduction V.topology A I false n).obj M)
      ⟶ N)
    (h : f.inverse.map (ConstantCompletion.insertion
        (ConstantCompletion.quotient V.topology A I n) M) ≫
        ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
          ((ConstantCompletion.reduction V.topology A I false n).obj M) ≫
        (ConstantCompletion.underlying (U.ring A)).map a =
      f.inverse.map (ConstantCompletion.insertion
        (ConstantCompletion.quotient V.topology A I n) M) ≫
        ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
          ((ConstantCompletion.reduction V.topology A I false n).obj M) ≫
        (ConstantCompletion.underlying (U.ring A)).map b) : a = b := by
  let η := (ConstantCompletion.scalarAdj
    (ConstantCompletion.quotient V.topology A I n)).unit.app M
  have := quotientUnit_epi V A I n M
  have := constantPullInsertion_isIso f A M
  apply (cancel_epi ((f.modulePull A).map η)).mp
  apply (ConstantCompletion.underlying (U.ring A)).map_injective
  apply (cancel_epi (ConstantCompletion.pullInsertion f.algebra
    (ConstantCompletion.constantMap f.algebra A) M)).mp
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    ← pullInsertion_naturality]
  simpa only [η, ConstantCompletion.insertion_eq_unit, Category.assoc,
    ConstantCompletion.reduction, ConstantCompletion.finiteMap] using h

-- Quotient-unit compatibility is independent of the pullback and is used on both sites.
private theorem reductionUnit_step (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (M : T.modules A) :
    (ConstantCompletion.scalarAdj (ConstantCompletion.quotient T.topology A I (n + 1))).unit.app
        M ≫ (ConstantCompletion.reductionStep T.topology A I false n).app M =
      (ConstantCompletion.scalarAdj (ConstantCompletion.quotient T.topology A I n)).unit.app
        M := by
  ext W m
  have ht := (ConstantCompletion.reductionStep_existsUnique T.topology A I false n).exists
    |>.choose_spec M W 1 m
  change ((ConstantCompletion.reductionStep T.topology A I false n).app M).val.app W
    (ConstantCompletion.tensorSection (ConstantCompletion.quotient T.topology A I (n + 1))
      M W 1 m) =
    ConstantCompletion.tensorSection (ConstantCompletion.quotient T.topology A I n) M W 1 m
  simpa only [ConstantCompletion.finiteMap, ConstantCompletion.reductionStep, map_one] using ht

/-- The ordinary strict reduction/pullback comparison is fixed on quotient-unit
insertions at every level. Its source and target are actual strict diagrams.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison).
Proof: at level n, whisker the normalized finite inverse-image/scalar-restriction
comparison by scalar extension along the quotient and compose with scalar restriction
of the inverse ordinary finite pullback comparison; their two insertion equations give
the levelwise normalization. The quotient scalar-extension unit is epic, the quotient
ring sheaf map being sectionwise surjective. Cancelling its inverse image shows that the
levels commute with the quotient transitions and that any normalized isomorphism agrees
with this one; levelwise invertibility makes the assembled tower map an isomorphism. -/
theorem Morphism.moduleReductionPullIso_existsUnique {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! e : ConstantCompletion.reductionTower V.topology A I false ⋙ f.towerModulePull A ≅
        f.modulePull A ⋙ ConstantCompletion.reductionTower U.topology A I false,
      Morphism.moduleReductionPullIso_normalized f A I e := by
  let P := f.modulePull A
  let av (n : ℕ) := ConstantCompletion.quotient V.topology A I n
  let au (n : ℕ) := ConstantCompletion.quotient U.topology A I n
  let rv (n : ℕ) := ConstantCompletion.change (av n) ⋙ ConstantCompletion.res (av n)
  let ru (n : ℕ) := ConstantCompletion.change (au n) ⋙ ConstantCompletion.res (au n)
  let ηv (n : ℕ) : 𝟭 (V.modules A) ⟶ rv n := (ConstantCompletion.scalarAdj (av n)).unit
  let ηu (n : ℕ) : 𝟭 (U.modules A) ⟶ ru n := (ConstantCompletion.scalarAdj (au n)).unit
  let er (n : ℕ) := f.finiteModuleRestrictionPullIso A I n
  let ef (n : ℕ) :=
    ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n
  have hr (n : ℕ) : Morphism.finiteModuleRestrictionPullIso_normalized f A I n (er n) :=
    (f.finiteModuleRestrictionPullIso_existsUnique A I n).exists.choose_spec
  have hf (n : ℕ) (M : V.modules A) :
      ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
          M ≫ ConstantCompletion.insertion (au n) (P.obj M) ≫
          (ConstantCompletion.underlying (ConstantCompletion.finite U.topology A I n)).map
            ((ef n).hom.app M) =
        f.inverse.map (ConstantCompletion.insertion (av n) M) ≫
          ConstantCompletion.pullInsertion f.algebra
            (ConstantCompletion.constantMap f.algebra (quotientRing A I n))
            ((ConstantCompletion.change (av n)).obj M) :=
    (ConstantCompletion.ordinaryFinitePull_existsUnique f.algebra f.direct f.adjunction
      A I n).exists.choose_spec M
  clear_value er ef
  let en (n : ℕ) : rv n ⋙ P ≅ P ⋙ ru n :=
    Functor.isoWhiskerLeft (ConstantCompletion.change (av n))
        (er n) ≪≫
      Functor.isoWhiskerRight (ef n).symm (ConstantCompletion.res (au n))
  have hn (n : ℕ) (M : V.modules A) :
      f.inverse.map (ConstantCompletion.insertion (av n) M) ≫
          ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
            ((rv n).obj M) ≫
          (ConstantCompletion.underlying (U.ring A)).map ((en n).hom.app M) =
        ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
          M ≫ ConstantCompletion.insertion (au n) (P.obj M) := by
    have hrn := hr n ((ConstantCompletion.change (av n)).obj M)
    have hfn := hf n M
    change _ ≫ _ ≫ (ConstantCompletion.underlying (U.ring A)).map
      ((er n).hom.app
          ((ConstantCompletion.change (av n)).obj M) ≫
        (ConstantCompletion.res (au n)).map
          ((ef n).inv.app
            M)) = _
    erw [Functor.map_comp, ← Category.assoc
      (ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
        ((rv n).obj M))
      ((ConstantCompletion.underlying (U.ring A)).map
        ((er n).hom.app ((ConstantCompletion.change (av n)).obj M)))
      ((ConstantCompletion.underlying (U.ring A)).map
        ((ConstantCompletion.res (au n)).map ((ef n).inv.app M))), hrn]
    rw [← Category.assoc]
    apply ((ConstantCompletion.underlying (ConstantCompletion.finite U.topology A I n)).mapIso
      ((ef n).app M))
        |>.comp_inv_eq.mpr
    simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using hfn.symm
  clear_value en
  have hunit (n : ℕ) (M : V.modules A) :
      P.map ((ηv n).app M) ≫ (en n).hom.app M = (ηu n).app (P.obj M) := by
    have := constantPullInsertion_isIso f A M
    apply (ConstantCompletion.underlying (U.ring A)).map_injective
    apply (cancel_epi (ConstantCompletion.pullInsertion f.algebra
      (ConstantCompletion.constantMap f.algebra A) M)).mp
    rw [Functor.map_comp, ← Category.assoc, ← pullInsertion_naturality]
    simpa only [ηv, ηu, ConstantCompletion.insertion_eq_unit, Category.assoc,
      ConstantCompletion.reduction, ConstantCompletion.finiteMap] using hn n M
  let dv (n : ℕ) : rv (n + 1) ⟶ rv n :=
    ConstantCompletion.reductionStep V.topology A I false n
  let du (n : ℕ) : ru (n + 1) ⟶ ru n :=
    ConstantCompletion.reductionStep U.topology A I false n
  have hv (n : ℕ) (M : V.modules A) :
      (ηv (n + 1)).app M ≫ (dv n).app M =
        (ηv n).app M :=
    reductionUnit_step V A I n M
  have hu (n : ℕ) (M : U.modules A) :
      (ηu (n + 1)).app M ≫ (du n).app M =
        (ηu n).app M :=
    reductionUnit_step U A I n M
  have hEpi (n : ℕ) (M : V.modules A) : Epi ((ηv n).app M) :=
    quotientUnit_epi V A I n M
  clear_value ηv ηu
  have hstep (M : V.modules A) (n : ℕ) :
      P.map ((dv n).app M) ≫
          (en n).hom.app M =
        (en (n + 1)).hom.app M ≫
          (du n).app (P.obj M) := by
    have := hEpi (n + 1) M
    apply (cancel_epi (P.map ((ηv (n + 1)).app M))).mp
    rw [← Category.assoc, ← P.map_comp, hv n M, hunit n M]
    rw [← Category.assoc, hunit (n + 1) M, hu n (P.obj M)]
  let q : ConstantCompletion.reductionTower V.topology A I false ⋙ f.towerModulePull A ⟶
      P ⋙ ConstantCompletion.reductionTower U.topology A I false :=
    { app := fun M ↦ NatTrans.ofOpSequence (fun n ↦ (en n).hom.app M) (fun n ↦ by
        change P.map (((Functor.ofOpSequence
          (ConstantCompletion.reductionStep V.topology A I false)).map
            (homOfLE (Nat.le_succ n)).op).app M) ≫ _ = _ ≫
          ((Functor.ofOpSequence (ConstantCompletion.reductionStep U.topology A I false)).map
            (homOfLE (Nat.le_succ n)).op).app (P.obj M)
        simpa only [Functor.ofOpSequence_map_homOfLE_succ, dv, du] using hstep M n)
      naturality := by
        intro M N a
        apply NatTrans.ext
        funext n
        exact (en n.unop).hom.naturality a }
  have (M : V.modules A) (n : ℕᵒᵖ) : IsIso ((q.app M).app n) := by
    change IsIso ((en n.unop).hom.app M)
    infer_instance
  have (M : V.modules A) : IsIso (q.app M) := NatIso.isIso_of_isIso_app _
  have : IsIso q := NatIso.isIso_of_isIso_app _
  refine ⟨asIso q, fun M n ↦ hn n M, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  apply reductionPull_hom_ext f A I n.unop M
  exact (he M n.unop).trans (hn n.unop M).symm

end

/-- The prescribed strict ordinary reduction/pullback isomorphism.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.moduleReductionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :=
  (f.moduleReductionPullIso_existsUnique A I).exists.choose

/-- The ordinary strict reduction comparison applied to a whole complex.
The iterated complex functors are explicit endpoints of the lifted square.
Its hom component is the original ordinary comparison applied degreewise.
Source: Stacks 07A4, 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.moduleReductionPullComplexIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :
    (ConstantCompletion.reductionTower V.topology A I false).mapHomologicalComplex (.up ℤ) ⋙
        (f.towerModulePull A).mapHomologicalComplex (.up ℤ) ≅
      (f.modulePull A).mapHomologicalComplex (.up ℤ) ⋙
        (ConstantCompletion.reductionTower U.topology A I false).mapHomologicalComplex (.up ℤ) :=
  letI := ConstantCompletion.reductionTower_additive V.topology A I false
  letI := ConstantCompletion.reductionTower_additive U.topology A I false
  letI := f.modulePull_additive A
  ConstantCompletion.mapComplexSquare
    (C := V.modules A) (D := V.towers A) (D' := U.modules A) (E := U.towers A)
    (ConstantCompletion.reductionTower V.topology A I false) (f.towerModulePull A)
    (f.modulePull A) (ConstantCompletion.reductionTower U.topology A I false)
    (f.moduleReductionPullIso A I)

attribute [local irreducible] Morphism.moduleReductionPullComplexIso
  ConstantCompletion.reductionTower

/-- A representative square with abstract endpoints. Keeping the equation abstract
prevents normalization from unfolding the concrete tensor and strict-tower functors.
Source: Stacks 099M, 06YY
(blueprint: def-pur-adic-site-strict-quotient-interface). -/
def comparisonSquareFormula
    {C H₁ H₂ H₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C] [Category H₁] [Category H₂] [Category H₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {q₀ : C ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃}
    {r : C ⥤ H₁} {b : C ⥤ H₂} {p : H₁ ⥤ H₃} {s : H₂ ⥤ H₃}
    {dr : D₀ ⥤ D₁} {db : D₀ ⥤ D₂} {dp : D₁ ⥤ D₃} {ds : D₂ ⥤ D₃}
    (α : q₀ ⋙ dr ⟶ r ⋙ q₁) (β : q₁ ⋙ dp ⟶ p ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s) (δ : q₀ ⋙ db ⟶ b ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s ⋙ q₃) (e : dr ⋙ dp ≅ db ⋙ ds) (X : C) : Prop :=
  e.hom.app (q₀.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X) =
    dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X)

private theorem resolving_comparisonSquare
    {M H₁ H₂ H₃ D₁ D₂ D₃ : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category H₁] [Category H₂] [Category H₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : H₁ ⥤ D₁) (q₂ : H₂ ⥤ D₂) (q₃ : H₃ ⥤ D₃)
    (r : CochainComplex M ℤ ⥤ H₁) (b : CochainComplex M ℤ ⥤ H₂)
    (p : H₁ ⥤ H₃) (s : H₂ ⥤ H₃)
    (dr : DerivedCategory M ⥤ D₁) (db : DerivedCategory M ⥤ D₂)
    (dp : D₁ ⥤ D₃) (ds : D₂ ⥤ D₃)
    (α : DerivedCategory.Q ⋙ dr ⟶ r ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p ⋙ q₃) (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b ⋙ q₂) (ε : q₂ ⋙ ds ⟶ s ⋙ q₃)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app (r.obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X))
    (hε : ∀ X, P X → IsIso (ε.app (b.obj X))) :
    ∃! e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X → comparisonSquareFormula α β γ δ ε e X := by
  obtain ⟨e, he, hu⟩ := ConstantCompletion.resolving_square_iso
    q₁ q₂ q₃ r b p s dr db dp ds α β γ δ ε P hres hα hβ hδ hε
  exact ⟨e, fun X hX ↦ (he X hX).symm,
    fun e' he' ↦ hu e' (fun X hX ↦ (he' X hX).symm)⟩

/-- The forward form of the abstract representative square, retaining the finite
pullback equation's original direction.
Source: Stacks 07A4, 099N
(blueprint: def-pur-adic-site-strict-quotient-interface). -/
def pullSquareFormula
    {C H₁ H₂ H₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C] [Category H₁] [Category H₂] [Category H₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {q₀ : C ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃}
    {r : C ⥤ H₁} {b : C ⥤ H₂} {p : H₁ ⥤ H₃} {s : H₂ ⥤ H₃}
    {dr : D₀ ⥤ D₁} {db : D₀ ⥤ D₂} {dp : D₁ ⥤ D₃} {ds : D₂ ⥤ D₃}
    (α : q₀ ⋙ dr ⟶ r ⋙ q₁) (β : q₁ ⋙ dp ⟶ p ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s) (δ : q₀ ⋙ db ⟶ b ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s ⋙ q₃) (e : dr ⋙ dp ≅ db ⋙ ds) (X : C) : Prop :=
  dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X) =
    e.hom.app (q₀.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X)

private theorem resolving_pullSquare
    {M H₁ H₂ H₃ D₁ D₂ D₃ : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category H₁] [Category H₂] [Category H₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : H₁ ⥤ D₁) (q₂ : H₂ ⥤ D₂) (q₃ : H₃ ⥤ D₃)
    (r : CochainComplex M ℤ ⥤ H₁) (b : CochainComplex M ℤ ⥤ H₂)
    (p : H₁ ⥤ H₃) (s : H₂ ⥤ H₃)
    (dr : DerivedCategory M ⥤ D₁) (db : DerivedCategory M ⥤ D₂)
    (dp : D₁ ⥤ D₃) (ds : D₂ ⥤ D₃)
    (α : DerivedCategory.Q ⋙ dr ⟶ r ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p ⋙ q₃) (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b ⋙ q₂) (ε : q₂ ⋙ ds ⟶ s ⋙ q₃)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app (r.obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X))
    (hε : ∀ X, P X → IsIso (ε.app (b.obj X))) :
    ∃! e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X → pullSquareFormula α β γ δ ε e X := by
  obtain ⟨e, he, hu⟩ := ConstantCompletion.resolving_square_iso
    q₁ q₂ q₃ r b p s dr db dp ds α β γ δ ε P hres hα hβ hδ hε
  exact ⟨e, fun X hX ↦ he X hX,
    fun e' he' ↦ hu e' (fun X hX ↦ he' X hX)⟩

/-- An evaluated representative square, followed by an exact restriction factor.
The abstract expression retains the original evaluation normalization verbatim.
Source: Stacks 0941, 099M
(blueprint: def-pur-adic-site-strict-quotient-interface). -/
def evaluationSquareFormula
    {C H₁ H₂ H₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C] [Category H₁] [Category H₂] [Category H₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {q₀ : C ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃}
    {r : C ⥤ H₁} {b : C ⥤ H₂} {p : H₁ ⥤ H₃} {s : H₂ ⥤ H₃}
    {dr : D₀ ⥤ D₁} {db : D₀ ⥤ D₂} {dp : D₁ ⥤ D₃} {ds : D₂ ⥤ D₃}
    (α : q₀ ⋙ dr ⟶ r ⋙ q₁) (β : q₁ ⋙ dp ⟶ p ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s) (δ : q₀ ⋙ db ⟶ b ⋙ q₂)
    (ε : s ⋙ q₃ ≅ q₂ ⋙ ds) (e : dr ⋙ dp ≅ db ⋙ ds) (X : C) : Prop :=
  e.hom.app (q₀.obj X) ≫ ds.map (δ.app X) =
    dp.map (α.app X) ≫ (β.app (r.obj X) ≫ q₃.map (γ.hom.app X)) ≫
      ε.hom.app (b.obj X)

private theorem resolving_evaluationSquare
    {M H₁ H₂ H₃ D₁ D₂ D₃ : Type*}
    [Category M] [Abelian M] [HasDerivedCategory M]
    [Category H₁] [Category H₂] [Category H₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : H₁ ⥤ D₁) (q₂ : H₂ ⥤ D₂) (q₃ : H₃ ⥤ D₃)
    (r : CochainComplex M ℤ ⥤ H₁) (b : CochainComplex M ℤ ⥤ H₂)
    (p : H₁ ⥤ H₃) (s : H₂ ⥤ H₃)
    (dr : DerivedCategory M ⥤ D₁) (db : DerivedCategory M ⥤ D₂)
    (dp : D₁ ⥤ D₃) (ds : D₂ ⥤ D₃)
    (α : DerivedCategory.Q ⋙ dr ⟶ r ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p ⋙ q₃) (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b ⋙ q₂) (ε : s ⋙ q₃ ≅ q₂ ⋙ ds)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app (r.obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X)) :
    ∃! e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X → evaluationSquareFormula α β γ δ ε e X := by
  obtain ⟨e, he, hu⟩ := resolving_comparisonSquare
    q₁ q₂ q₃ r b p s dr db dp ds α β γ δ ε.inv P hres hα hβ hδ
    (fun X _ ↦ by infer_instance)
  have hf (e' : dr ⋙ dp ≅ db ⋙ ds) (X : CochainComplex M ℤ) :
      comparisonSquareFormula α β γ δ ε.inv e' X ↔
        evaluationSquareFormula α β γ δ ε e' X := by
    dsimp only [comparisonSquareFormula, evaluationSquareFormula]
    simp only [← Category.assoc]
    exact Iso.comp_inv_eq (ε.app (b.obj X))
  exact ⟨e, fun X hX ↦ (hf e X).1 (he X hX),
    fun e' he' ↦ hu e' (fun X hX ↦ (hf e' X).2 (he' X hX))⟩

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.reductionPullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A)
    (e : V.reduction A I ⋙ f.towerPull A ≅ f.pull A ⋙ U.reduction A I) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    comparisonSquareFormula
      (ConstantCompletion.quotientPresentation V.topology A I false).comparison
      (f.towerModulePull A).mapDerivedCategoryFactors.hom
      (f.moduleReductionPullComplexIso A I)
      (f.modulePull A).mapDerivedCategoryFactors.hom
      (ConstantCompletion.quotientPresentation U.topology A I false).comparison e P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The strict derived comparison is uniquely characterized on a single flat-term
K-flat representative, with the entire strict ordinary comparison applied termwise.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison).
Proof: exact inverse image preserves flat K-flat representatives. The diagonal of
one such representative is K-flat on the diagram site, so it computes reduction
against the whole quotient diagram. Apply moduleReductionPullIso termwise, insert
the universal reduction comparisons and the exact-pullback factorizations, then
descend along localization. Every object has such a representative, proving uniqueness. -/
theorem Morphism.reductionPullIso_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! e : V.reduction A I ⋙ f.towerPull A ≅ f.pull A ⋙ U.reduction A I,
      Morphism.reductionPullIso_normalized f A I e := by
  let P (K : CochainComplex (V.modules A) ℤ) :=
    K.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, (K.X q).IsFlat
  obtain ⟨e, he, hu⟩ := resolving_comparisonSquare (M := V.modules A)
    (ConstantCompletion.TQ (V.ring A)) (ConstantCompletion.Q (U.ring A))
    (ConstantCompletion.TQ (U.ring A))
    ((ConstantCompletion.reductionTower V.topology A I false).mapHomologicalComplex (.up ℤ))
    ((f.modulePull A).mapHomologicalComplex (.up ℤ))
    ((f.towerModulePull A).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.reductionTower U.topology A I false).mapHomologicalComplex (.up ℤ))
    (V.reduction A I) (f.pull A) (f.towerPull A) (U.reduction A I)
    (ConstantCompletion.quotientPresentation V.topology A I false).comparison
    (f.towerModulePull A).mapDerivedCategoryFactors.hom
    (f.moduleReductionPullComplexIso A I)
    (f.modulePull A).mapDerivedCategoryFactors.hom
    (ConstantCompletion.quotientPresentation U.topology A I false).comparison
    P (V.flat_kFlat_resolution A)
    (fun K hK ↦ (ConstantCompletion.quotientPresentation V.topology A I false
      ).laws.2.1 K ((Site.isAcyclicTensorKFlat_iff K).1 hK.1) hK.2)
    (fun K _ ↦ by infer_instance)
    (fun K _ ↦ by infer_instance)
    (fun K hK ↦ by
      have h := ConstantCompletion.pull_flat_kFlat f.algebra f.direct f.adjunction
        (ConstantCompletion.constantMap f.algebra A) K hK.1 hK.2
      exact (ConstantCompletion.quotientPresentation U.topology A I false
        ).laws.2.1 _ ((Site.isAcyclicTensorKFlat_iff _).1 h.1) h.2)
  exact ⟨e, fun K hk hf ↦ he K ⟨hk, hf⟩,
    fun e' he' ↦ hu e' (fun K hK ↦ he' K hK.1 hK.2)⟩

/-- The uniquely normalized derived reduction/pullback comparison.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.reductionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :=
  (f.reductionPullIso_existsUnique A I).exists.choose

/-- The whole-diagram projection is the tower adjunct of counit tensored with identity.
The preceding reduction comparison is the canonical tensor/pullback identification.
Source: Stacks 0B56, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.towerProjection {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : U.derived A) :
    (V.reduction A I).obj ((f.push A).obj K) ⟶
      (f.towerPush A).obj ((U.reduction A I).obj K) :=
  (f.towerAdjunction A).homEquiv _ _
    ((f.reductionPullIso A I).hom.app ((f.push A).obj K) ≫
      (U.reduction A I).map ((f.adj A).counit.app K))

/-- The comparison H is inverse horizontal pullback/reduction comparison followed by
horizontal pullback of the strict projection adjunct, exactly in the specified direction.
Source: Stacks 0B56, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def projectionComparison {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] (I : Ideal A) (K : X.derived A) :
    (Y'.reduction A I).obj ((g.pull A).obj ((f.push A).obj K)) ⟶
      (g.towerPull A).obj ((f.towerPush A).obj ((X.reduction A I).obj K)) :=
  (g.reductionPullIso A I).inv.app ((f.push A).obj K) ≫
    (g.towerPull A).map (f.towerProjection A I K)

/-- Each positive quotient is perfect as an A-complex: bounded finite projectives.
Source: smooth-purity blueprint, proposition-composition-base-change-rf-shriek Step 4
(blueprint: lem-sp-completion-mate-comparison). -/
def PerfectQuotients (A : Type u) [CommRing A] (I : Ideal A) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  ∀ n : ℕ, DerivedCategory.IsPerfectRingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ I ^ (n + 1))))

/-- Exact evaluation of a strict tower, before localization.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.evaluateModule (T : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :=
  (evaluation ℕᵒᵖ (T.modules A)).obj (op n)

/-- Exact evaluation after deriving the strict diagram category.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.evaluate (T : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :=
  (T.evaluateModule A n).mapDerivedCategory

/-- Termwise inverse image commutes with ordinary evaluation by identity components.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluateModulePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :
    f.towerModulePull A ⋙ U.evaluateModule A n ≅ V.evaluateModule A n ⋙ f.modulePull A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)

/-- The canonical derived evaluation/inverse-image comparison.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluatePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :
    f.towerPull A ⋙ U.evaluate A n ≅ V.evaluate A n ⋙ f.pull A :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (f.evaluateModulePullIso A n) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The complex-level universal derived-direct-image unit, from the existing K-injective
right-derived functor, with no new choice.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.pushUnit {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (P : CochainComplex (U.modules A) ℤ) :
    (ConstantCompletion.Q (V.ring A)).obj (((f.modulePush A).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (f.push A).obj ((ConstantCompletion.Q (U.ring A)).obj P) :=
  cast (by rfl)
    ((f.modulePush A).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The same universal unit for derived termwise direct image of strict towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.towerPushUnit {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (P : CochainComplex (U.towers A) ℤ) :
    (ConstantCompletion.TQ (V.ring A)).obj
        (((f.towerModulePush A).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (f.towerPush A).obj ((ConstantCompletion.TQ (U.ring A)).obj P) :=
  cast (by rfl)
    ((f.towerModulePush A).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluatePushIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ)
    (e : f.towerPush A ⋙ V.evaluate A n ≅ U.evaluate A n ⋙ f.push A) : Prop :=
  ∀ P : CochainComplex (U.towers A) ℤ,
    (V.evaluate A n).map (f.towerPushUnit A P) ≫
        e.hom.app ((ConstantCompletion.TQ (U.ring A)).obj P) ≫
        (f.push A).map ((U.evaluateModule A n).mapDerivedCategoryFactors.hom.app P) =
      (V.evaluateModule A n).mapDerivedCategoryFactors.hom.app
        (((f.towerModulePush A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      f.pushUnit A (((U.evaluateModule A n).mapHomologicalComplex (.up ℤ)).obj P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def rightCochainUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app X := F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj X)
  naturality _X _Y f := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightCochainUnit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (X : CochainComplex C ℤ) (hX : X.IsKInjective) :
    IsIso ((rightCochainUnit F).app X) := by
  have := hX
  change IsIso (F.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj X))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem right_normalized_unique
    {C D H : Type*} [Category C] [Category D] [Category H]
    (q : C ⥤ D) (W : MorphismProperty C) [q.IsLocalization W]
    (F G : D ⥤ H) (T : C ⥤ H) (α : T ⟶ q ⋙ F) (β : T ⟶ q ⋙ G)
    [F.IsRightDerivedFunctor α W] [G.IsRightDerivedFunctor β W] :
    ∃! e : F ≅ G, ∀ X, α.app X ≫ e.hom.app (q.obj X) = β.app X := by
  let e := Functor.rightDerivedUnique F G α β W
  have he (X : C) : α.app X ≫ e.hom.app (q.obj X) = β.app X := by
    simpa only [e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app F G α β W (𝟙 T) X
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Functor.rightDerived_ext F α W
  apply NatTrans.ext
  funext X
  exact (he' X).trans (he X).symm

private theorem normalized_square_iff
    {C : Type*} [Category C] {X X' Y Y' Z : C}
    (a : X' ≅ X) (b : Y' ≅ Y) (u : X' ⟶ Z) (v : X ⟶ Y) (w : Z ⟶ Y') :
    ((a.inv ≫ u) ≫ w = v ≫ b.inv) ↔ (u ≫ w ≫ b.hom = a.hom ≫ v) := by
  constructor
  · intro h
    apply (cancel_epi a.inv).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun t ↦ t ≫ b.hom) h
  · intro h
    apply (cancel_mono b.hom).1
    simp only [Category.assoc, h, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation/direct-image comparison with its universal-unit normalization on all
strict tower complexes, and therefore its prescribed K-injective computation.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: evaluation has an exact left adjoint, so preserves K-injectives. A K-injective
tower thus computes both direct images after evaluation. The ordinary composites
are identical. Their universal derived units give the displayed square; localization
and K-injective representatives make the resulting natural isomorphism unique. -/
theorem Morphism.evaluatePushIso_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :
    ∃! e : f.towerPush A ⋙ V.evaluate A n ≅ U.evaluate A n ⋙ f.push A,
      Morphism.evaluatePushIso_normalized f A n e := by
  let : Abelian (U.modules A) :=
    { (inferInstance : Abelian (U.modules A)) with
      toPreadditive := (inferInstance : Preadditive (U.modules A)) }
  let : Abelian (V.modules A) :=
    { (inferInstance : Abelian (V.modules A)) with
      toPreadditive := (inferInstance : Preadditive (V.modules A)) }
  let : Abelian (U.towers A) :=
    { (inferInstance : Abelian (U.towers A)) with
      toPreadditive := (inferInstance : Preadditive (U.towers A)) }
  let : Abelian (V.towers A) :=
    { (inferInstance : Abelian (V.towers A)) with
      toPreadditive := (inferInstance : Preadditive (V.towers A)) }
  let := HasDerivedCategory.standard (U.modules A)
  let := HasDerivedCategory.standard (V.modules A)
  let := HasDerivedCategory.standard (U.towers A)
  let := HasDerivedCategory.standard (V.towers A)
  have := U.hasKInjectives A
  have := U.towersHasKInjectives A
  let E := U.evaluateModule A n
  let E' := V.evaluateModule A n
  let G := f.modulePush A
  let Gt := f.towerModulePush A
  obtain ⟨α, hα, hαapp⟩ := towerComparison_existsComposite Gt E'
    (f.towerPush A) (V.evaluate A n) (rightCochainUnit Gt)
    E'.mapDerivedCategoryFactors.inv (rightCochainUnit_isIso Gt)
    (fun _ _ ↦ inferInstance)
  obtain ⟨β, hβ, hβapp⟩ := towerComparison_existsComposite E G
    (U.evaluate A n) (f.push A) E.mapDerivedCategoryFactors.inv
    (rightCochainUnit G) (fun _ _ ↦ inferInstance)
    (fun X hX ↦ by
      have := hX
      exact rightCochainUnit_isIso G _ (tower_evaluation_isKInjective (U.modules A) X (op n)))
  have := hα
  have := hβ
  obtain ⟨e, he, hu⟩ := right_normalized_unique
    (ConstantCompletion.TQ (U.ring A))
    (HomologicalComplex.quasiIso (U.towers A) (.up ℤ))
    (f.towerPush A ⋙ V.evaluate A n) (U.evaluate A n ⋙ f.push A)
    _ α β
  have norm (e' : f.towerPush A ⋙ V.evaluate A n ≅ U.evaluate A n ⋙ f.push A) :
      (∀ X, α.app X ≫ e'.hom.app ((ConstantCompletion.TQ (U.ring A)).obj X) = β.app X) ↔
        f.evaluatePushIso_normalized A n e' := by
    have hn (X : CochainComplex (U.towers A) ℤ) :=
      normalized_square_iff
        (E'.mapDerivedCategoryFactors.app ((Gt.mapHomologicalComplex (.up ℤ)).obj X))
        ((f.push A).mapIso (E.mapDerivedCategoryFactors.app X))
        ((V.evaluate A n).map (f.towerPushUnit A X))
        (f.pushUnit A ((E.mapHomologicalComplex (.up ℤ)).obj X))
    constructor
    · intro h X
      exact (hn X (e'.hom.app _)).1 (by
        have hx := h X
        rw [hαapp, hβapp] at hx
        exact hx)
    · intro h X
      rw [hαapp, hβapp]
      exact (hn X (e'.hom.app _)).2 (h X)
  exact ⟨e, (norm e).1 he, fun e' he' ↦ hu e' ((norm e').2 he')⟩

/-- The specified derived evaluation/direct-image isomorphism.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluatePushIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :=
  (f.evaluatePushIso_existsUnique A n).exists.choose

/-- Reduction retaining the finite quotient coefficient category.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.finiteReduction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  ConstantCompletion.extend (ConstantCompletion.quotient T.topology A I n)

/-- Restriction from the finite coefficient category to the original A-coefficients.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.finiteRestriction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  ConstantCompletion.dres (ConstantCompletion.quotient T.topology A I n)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteModuleAdjunction_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (adj : ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n) ⊣
        ConstantCompletion.res (ConstantCompletion.quotient T.topology A I n)) : Prop :=
  ∀ (M : T.modules A) (N : T.modules (quotientRing A I n))
    (a : (ConstantCompletion.change
      (ConstantCompletion.quotient T.topology A I n)).obj M ⟶ N),
    (ConstantCompletion.underlying (T.ring A)).map (adj.homEquiv M N a) =
      ConstantCompletion.insertion (ConstantCompletion.quotient T.topology A I n) M ≫
        (ConstantCompletion.underlying (T.ring (quotientRing A I n))).map a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized ordinary scalar-extension adjunction, fixed by insertion of 1.
Source: Stacks 03CU (blueprint: lem-sp-completion-mate-comparison).
Proof: the tensor/sheafification universal property sends a linear map out of a
scalar extension to its restriction along m mapped to 1 tensor m. The inverse sends
s tensor m to s times the image of m. The balanced relations and sheafification
prove the inverse identities. This determines the hom bijection uniquely. -/
theorem Site.finiteModuleAdjunction_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! adj : ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n) ⊣
        ConstantCompletion.res (ConstantCompletion.quotient T.topology A I n),
      Site.finiteModuleAdjunction_normalized T A I n adj := by
  let c := ConstantCompletion.quotient T.topology A I n
  let adj : ConstantCompletion.change c ⊣ ConstantCompletion.res c :=
    SheafOfModules.tensorAdjunction c
  have hunit (M : T.modules A) : ConstantCompletion.insertion c M =
      SheafOfModules.tensorUnit c M := by
    ext U m
    exact ((ConstantCompletion.insertion_existsUnique c M).exists.choose_spec U m).trans
      (SheafOfModules.tensorUnit_apply c M U m).symm
  have hn : T.finiteModuleAdjunction_normalized A I n adj := by
    intro M N a
    change (ConstantCompletion.underlying (T.ring A)).map
      ((SheafOfModules.tensorAdjunction c).homEquiv M N a) = _
    rw [Adjunction.homEquiv_unit, Functor.map_comp, hunit]
    rfl
  refine ⟨adj, hn, ?_⟩
  intro adj' hn'
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply (ConstantCompletion.underlying (T.ring A)).map_injective
  rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_id,
    hn' M _ (𝟙 _), hn M _ (𝟙 _)]

/-- The tensor-unit normalized module extension/restriction adjunction.
Source: Stacks 03CU (blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteModuleAdjunction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  (T.finiteModuleAdjunction_existsUnique A I n).exists.choose

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteAdjunction_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (adj : T.finiteReduction A I n ⊣ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    adj.unit.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
        (T.finiteRestriction A I n).map
          ((ConstantCompletion.extendComparison
            (ConstantCompletion.quotient T.topology A I n)).app P) =
      (ConstantCompletion.Q (T.ring A)).map ((NatTrans.mapHomologicalComplex
        (T.finiteModuleAdjunction A I n).unit (.up ℤ)).app P) ≫
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)).hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_left_universal
    {M H : Type*} [Category M] [Abelian M] [HasDerivedCategory M] [Category H]
    (G : DerivedCategory M ⥤ H) (T : CochainComplex M ℤ ⥤ H)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (α : DerivedCategory.Q ⋙ G ⟶ T)
    (hα : ∀ X, P X → IsIso (α.app X)) :
    G.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso M (.up ℤ)) := by
  classical
  have lifts (s : Functor.RightExtension (DerivedCategory.Q (C := M)) T) :
      ∃! e : s.left ⟶ G, Functor.whiskerLeft DerivedCategory.Q e ≫ α = s.hom := by
    obtain ⟨e, he, hu⟩ := ConstantCompletion.resolving_comparison s.left G T P hres
      s.hom α hα
    refine ⟨e, ?_, ?_⟩
    · apply NatTrans.ext
      funext X
      obtain ⟨K, f, hK, hf⟩ := hres X
      have : QuasiIso f := hf
      have : IsIso (s.left.map (DerivedCategory.Q.map f)) := inferInstance
      apply (cancel_epi (s.left.map (DerivedCategory.Q.map f))).1
      change s.left.map (DerivedCategory.Q.map f) ≫
        (e.app (DerivedCategory.Q.obj X) ≫ α.app X) =
        s.left.map (DerivedCategory.Q.map f) ≫ s.hom.app X
      have hn : G.map (DerivedCategory.Q.map f) ≫ α.app X = α.app K ≫ T.map f :=
        α.naturality f
      rw [← Category.assoc, e.naturality, Category.assoc, hn,
        ← Category.assoc, he K hK]
      exact (s.hom.naturality f).symm
    · intro e' he'
      apply hu e'
      intro X hX
      exact congrArg (fun a ↦ a.app X) he'
  choose lift fac uniq using lifts
  refine ⟨⟨⟨IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk (lift s) (fac s)) ?_⟩⟩⟩
  intro s m
  apply CostructuredArrow.hom_ext
  exact uniq s m.left (CostructuredArrow.w m)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived extension/restriction adjunction with its unit fixed on K-flat representatives.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison).
Proof: derive the tensor-unit normalized ordinary adjunction. Exact restriction and
K-flat scalar-extension computation give the displayed equation for its unit. Every
object has a K-flat representative, so this equation determines the unit and hence
the adjunction uniquely. -/
theorem Site.finiteAdjunction_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! adj : T.finiteReduction A I n ⊣ T.finiteRestriction A I n,
      Site.finiteAdjunction_normalized T A I n adj := by
  let : Abelian (T.modules A) :=
    { (inferInstance : Abelian (T.modules A)) with
      toPreadditive := (inferInstance : Preadditive (T.modules A)) }
  let : Abelian (T.modules (quotientRing A I n)) :=
    { (inferInstance : Abelian (T.modules (quotientRing A I n))) with
      toPreadditive := (inferInstance : Preadditive (T.modules (quotientRing A I n))) }
  let := HasDerivedCategory.standard (T.modules A)
  let := HasDerivedCategory.standard (T.modules (quotientRing A I n))
  let c := ConstantCompletion.quotient T.topology A I n
  let W := HomologicalComplex.quasiIso (T.modules A) (.up ℤ)
  let W' := HomologicalComplex.quasiIso (T.modules (quotientRing A I n)) (.up ℤ)
  let L := ConstantCompletion.change c
  let R := ConstantCompletion.res c
  let α := ConstantCompletion.extendComparison c
  let β := (ConstantCompletion.resFactors c).hom
  let P (X : CochainComplex (T.modules A) ℤ) :=
    X.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, (X.X q).IsFlat
  have : (T.finiteReduction A I n).IsLeftDerivedFunctor α W :=
    (ConstantCompletion.derivedExtension c).universal
  have : (T.finiteRestriction A I n).IsRightDerivedFunctor β W' :=
    Functor.isRightDerivedFunctor_of_inverts W' _ (ConstantCompletion.resFactors c).symm
  have : (T.finiteReduction A I n ⋙ T.finiteRestriction A I n).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight α (T.finiteRestriction A I n)) W := by
    apply resolving_left_universal _ _ P
      (T.flat_kFlat_resolution A)
    intro X hX
    have : IsIso (α.app X) := (ConstantCompletion.derivedExtension c).computation X
      ((Site.isAcyclicTensorKFlat_iff X).1 hX.1)
    dsimp only [NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app]
    infer_instance
  have : (T.finiteRestriction A I n ⋙ T.finiteReduction A I n).IsRightDerivedFunctor
      (Functor.whiskerRight β (T.finiteReduction A I n) ≫
        (Functor.associator _ _ _).hom) W' :=
    Functor.isRightDerivedFunctor_of_inverts W' _
      ((Functor.isoWhiskerRight (ConstantCompletion.resFactors c)
        (T.finiteReduction A I n)) ≪≫ Functor.associator _ _ _).symm
  let adj := (T.finiteModuleAdjunction A I n).mapHomologicalComplex (.up ℤ)
  let ad := adj.derived W W' α β
  have hn : T.finiteAdjunction_normalized A I n ad := by
    intro X _
    exact adj.derivedη_fac_app W α β X
  refine ⟨ad, hn, ?_⟩
  intro ad' hn'
  apply Adjunction.ext
  apply ConstantCompletion.resolving_nat_ext P
    (T.flat_kFlat_resolution A)
  intro X hX
  have : IsIso (α.app X) := (ConstantCompletion.derivedExtension c).computation X
      ((Site.isAcyclicTensorKFlat_iff X).1 hX.1)
  apply (cancel_mono ((T.finiteRestriction A I n).map (α.app X))).1
  exact (hn' X hX.1).trans (hn X hX.1).symm

/-- The specified derived finite scalar-extension adjunction.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteAdjunction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  (T.finiteAdjunction_existsUnique A I n).exists.choose

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteEvaluationIso_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    evaluationSquareFormula
      (ConstantCompletion.quotientPresentation T.topology A I false).comparison
      (T.evaluateModule A n).mapDerivedCategoryFactors.hom
      (ConstantCompletion.quotientEvaluationComplexIso T.topology A I n)
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient T.topology A I n))
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)) e P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The evaluated strict quotient object is the restricted finite scalar extension,
with its comparison fixed by the two universal reduction counits.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: on a single K-flat complex, evaluation of its strict quotient diagram is
its finite quotient tensor complex. Compose the universal comparison maps and the
exact restriction factorization. Descend; K-flat resolutions prove uniqueness. -/
theorem Site.finiteEvaluationIso_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n,
      Site.finiteEvaluationIso_normalized T A I n e := by
  let c := ConstantCompletion.quotient T.topology A I n
  let P (K : CochainComplex (T.modules A) ℤ) :=
    K.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, (K.X q).IsFlat
  obtain ⟨e, he, hu⟩ := resolving_evaluationSquare (M := T.modules A)
    (ConstantCompletion.TQ (T.ring A))
    (ConstantCompletion.Q (T.ring (quotientRing A I n)))
    (ConstantCompletion.Q (T.ring A))
    ((ConstantCompletion.reductionTower T.topology A I false).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.change c).mapHomologicalComplex (.up ℤ))
    ((T.evaluateModule A n).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.res c).mapHomologicalComplex (.up ℤ))
    (T.reduction A I) (T.finiteReduction A I n)
    (T.evaluate A n) (T.finiteRestriction A I n)
    (ConstantCompletion.quotientPresentation T.topology A I false).comparison
    (T.evaluateModule A n).mapDerivedCategoryFactors.hom
    (ConstantCompletion.quotientEvaluationComplexIso T.topology A I n)
    (ConstantCompletion.extendComparison c) (ConstantCompletion.resFactors c)
    P (T.flat_kFlat_resolution A)
    (fun K hK ↦ (ConstantCompletion.quotientPresentation T.topology A I false
      ).laws.2.1 K ((Site.isAcyclicTensorKFlat_iff K).1 hK.1) hK.2)
    (fun K _ ↦ by infer_instance)
    (fun K hK ↦ (ConstantCompletion.derivedExtension c).computation K
      ((Site.isAcyclicTensorKFlat_iff K).1 hK.1))
  exact ⟨e, fun K hk hf ↦ he K ⟨hk, hf⟩,
    fun e' he' ↦ hu e' (fun K hK ↦ he' K hK.1 hK.2)⟩

/-- The canonical evaluation/finite-restriction comparison.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteEvaluationIso (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  (T.finiteEvaluationIso_existsUnique A I n).exists.choose

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finitePullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n)) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    pullSquareFormula
      (f.modulePull A).mapDerivedCategoryFactors.hom
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient U.topology A I n))
      (ConstantCompletion.mapComplexSquare (f.modulePull A)
        (ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n))
        (ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n))
        (f.modulePull (quotientRing A I n))
        (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n))
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient V.topology A I n))
      (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom e P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite coefficient tensor/pullback comparison, fixed by ordinary tensor
reassociation on flat-term K-flat representatives.
Source: Stacks 07A4, 099N (blueprint: lem-sp-completion-mate-comparison).
Proof: apply ConstantCompletion.ordinaryFinitePull on a K-flat representative.
Exact pullback and scalar extension preserve these representatives. Insert the
universal counits on each side, then descend by localization. The representative
formula determines the natural isomorphism uniquely. -/
theorem Morphism.finitePullIso_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n),
      Morphism.finitePullIso_normalized f A I n e := by
  let c := ConstantCompletion.quotient V.topology A I n
  let c' := ConstantCompletion.quotient U.topology A I n
  let P (K : CochainComplex (V.modules A) ℤ) :=
    K.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, (K.X q).IsFlat
  obtain ⟨e, he, hu⟩ := resolving_pullSquare (M := V.modules A)
    (ConstantCompletion.Q (U.ring A))
    (ConstantCompletion.Q (V.ring (quotientRing A I n)))
    (ConstantCompletion.Q (U.ring (quotientRing A I n)))
    ((f.modulePull A).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.change c).mapHomologicalComplex (.up ℤ))
    ((ConstantCompletion.change c').mapHomologicalComplex (.up ℤ))
    ((f.modulePull (quotientRing A I n)).mapHomologicalComplex (.up ℤ))
    (f.pull A) (V.finiteReduction A I n) (U.finiteReduction A I n)
    (f.pull (quotientRing A I n))
    (f.modulePull A).mapDerivedCategoryFactors.hom
    (ConstantCompletion.extendComparison c')
    (ConstantCompletion.mapComplexSquare (f.modulePull A)
      (ConstantCompletion.change c') (ConstantCompletion.change c)
      (f.modulePull (quotientRing A I n))
      (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n))
    (ConstantCompletion.extendComparison c)
    (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom
    P (V.flat_kFlat_resolution A)
    (fun K _ ↦ by infer_instance)
    (fun K hK ↦ (ConstantCompletion.derivedExtension c').computation _
      ((Site.isAcyclicTensorKFlat_iff _).1
        (ConstantCompletion.pull_flat_kFlat f.algebra f.direct f.adjunction
          (ConstantCompletion.constantMap f.algebra A) K hK.1 hK.2).1))
    (fun K hK ↦ (ConstantCompletion.derivedExtension c).computation K
      ((Site.isAcyclicTensorKFlat_iff K).1 hK.1))
    (fun K _ ↦ by infer_instance)
  exact ⟨e, fun K hk hf ↦ he K ⟨hk, hf⟩,
    fun e' he' ↦ hu e' (fun K hK ↦ he' K hK.1 hK.2)⟩

/-- The canonical derived finite tensor/pullback comparison.
Source: Stacks 07A4, 099N (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finitePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :=
  (f.finitePullIso_existsUnique A I n).exists.choose

/-- Direct image commutes with finite scalar restriction by adjunction conjugation
of the canonical scalar-extension/pullback comparison.
Source: Stacks 06YY, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteRestrictionPushIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    U.finiteRestriction A I n ⋙ f.push A ≅
      f.push (quotientRing A I n) ⋙ V.finiteRestriction A I n :=
  conjugateIsoEquiv ((f.adj A).comp (U.finiteAdjunction A I n))
    ((V.finiteAdjunction A I n).comp (f.adj (quotientRing A I n)))
      (f.finitePullIso A I n).symm

/-- Its exact derived comparison, retaining the finite quotient coefficient ring.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteRestrictionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    V.finiteRestriction A I n ⋙ f.pull A ≅
      f.pull (quotientRing A I n) ⋙ U.finiteRestriction A I n :=
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient V.topology A I n)).1
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient V.topology A I n)).2
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient U.topology A I n)).1
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient U.topology A I n)).2
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (f.finiteModuleRestrictionPullIso A I n) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The canonical finite-coefficient realization of the evaluated source B.
It uses evaluation of direct image, quotient evaluation, and the actual finite
restriction comparisons. It does not refer to either exchange transformation.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def finiteSourceIso {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : X.derived A) :
    (Y'.evaluate A n).obj
        ((g.towerPull A).obj ((f.towerPush A).obj ((X.reduction A I).obj K))) ≅
      (Y'.finiteRestriction A I n).obj
        ((g.pull (quotientRing A I n)).obj
          ((f.push (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))) :=
  (g.evaluatePullIso A n).app ((f.towerPush A).obj ((X.reduction A I).obj K)) ≪≫
    (g.pull A).mapIso ((f.evaluatePushIso A n).app ((X.reduction A I).obj K)) ≪≫
    (g.pull A).mapIso ((f.push A).mapIso ((X.finiteEvaluationIso A I n).app K)) ≪≫
    (g.pull A).mapIso ((f.finiteRestrictionPushIso A I n).app
      ((X.finiteReduction A I n).obj K)) ≪≫
    (g.finiteRestrictionPullIso A I n).app
      ((f.push (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))

/-- The analogous finite-coefficient realization of the evaluated target D,
constructed independently of the exchange maps.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def finiteTargetIso {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : X.derived A) :
    (Y'.evaluate A n).obj
        ((k.towerPush A).obj ((h.towerPull A).obj ((X.reduction A I).obj K))) ≅
      (Y'.finiteRestriction A I n).obj
        ((k.push (quotientRing A I n)).obj
          ((h.pull (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))) :=
  (k.evaluatePushIso A n).app ((h.towerPull A).obj ((X.reduction A I).obj K)) ≪≫
    (k.push A).mapIso ((h.evaluatePullIso A n).app ((X.reduction A I).obj K)) ≪≫
    (k.push A).mapIso ((h.pull A).mapIso ((X.finiteEvaluationIso A I n).app K)) ≪≫
    (k.push A).mapIso ((h.finiteRestrictionPullIso A I n).app
      ((X.finiteReduction A I n).obj K)) ≪≫
    (k.finiteRestrictionPushIso A I n).app
      ((h.pull (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))

/-- The finite projection map with coefficients retained in A/I^(n+1), obtained by
transposing finite tensor/pullback comparison followed by the ordinary derived counit.
Source: Stacks 0B56, 0944 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteProjection {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : U.derived A) :
    (V.finiteReduction A I n).obj ((f.push A).obj K) ⟶
      (f.push (quotientRing A I n)).obj ((U.finiteReduction A I n).obj K) :=
  (f.adj (quotientRing A I n)).homEquiv _ _
    ((f.finitePullIso A I n).inv.app ((f.push A).obj K) ≫
      (U.finiteReduction A I n).map ((f.adj A).counit.app K))

/-- The finite projection comparison corresponding to H, before scalar restriction.
Source: Stacks 0B56, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def finiteProjectionComparison {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : X.derived A) :
    (Y'.finiteReduction A I n).obj ((g.pull A).obj ((f.push A).obj K)) ⟶
      (g.pull (quotientRing A I n)).obj
        ((f.push (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K)) :=
  (g.finitePullIso A I n).hom.app ((f.push A).obj K) ≫
    (g.pull (quotientRing A I n)).map (f.finiteProjection A I n K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality needed to form s as an actual natural transformation.
Source: Stacks 0B56, 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: reductionPullIso is natural, the derived counit is natural, and transposition
is natural in both arguments. Hence towerProjection and H are natural in K. Apply
the limit functor and restrict to the complete full subcategory. -/
theorem comparisonS_naturality {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K L : X.Complete A I) (a : K ⟶ L) :
    (f.completePush A I ⋙ g.completePull A I ⋙
        ObjectProperty.ι (Y'.IsComplete A I)).map a ≫
        (Y'.rlim A).map (projectionComparison (f := f) (g := g) A I L.obj) =
      (Y'.rlim A).map (projectionComparison (f := f) (g := g) A I K.obj) ≫
        (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
          f.towerPush A ⋙ g.towerPull A ⋙ Y'.rlim A).map a := by
  let p := (mateEquiv (f.adj A) (f.towerAdjunction A)
    (TwoSquare.mk _ _ _ _ (f.reductionPullIso A I).hom))
  have hp (M : X.derived A) : p.app M = f.towerProjection A I M := by
    simp [p, Morphism.towerProjection, Adjunction.homEquiv_unit,
      Functor.map_comp]
  let H := Functor.whiskerLeft (f.push A) (g.reductionPullIso A I).inv ≫
    Functor.whiskerRight p (g.towerPull A)
  have hH (M : X.derived A) :
      H.app M = projectionComparison (f := f) (g := g) A I M := by
    simp only [H, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, hp, projectionComparison]
  change (Y'.rlim A).map ((Y'.reduction A I).map
      ((g.pull A).map ((f.push A).map a.hom))) ≫ _ = _
  simpa only [Functor.whiskerRight_app, hH, Functor.comp_map, ObjectProperty.ι_map] using
    (Functor.whiskerRight H (Y'.rlim A)).naturality a.hom

/-- The specified map s, namely total derived inverse limit of H.
Source: Stacks 099M, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def comparisonS {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    f.completePush A I ⋙ g.completePull A I ⋙ ObjectProperty.ι (Y'.IsComplete A I) ⟶
      ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
        f.towerPush A ⋙ g.towerPull A ⋙ Y'.rlim A where
  app K := (Y'.rlim A).map (projectionComparison (f := f) (g := g) A I K.obj)
  naturality K L a := comparisonS_naturality A I K L a

/-- The prescribed direct-image/limit comparison at K, with the reduction/pullback
identification inserted. Its definition is independent of either exchange map.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison). -/
def comparisonTComponent {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (K : X.Complete A I) :
    ((h.completePull A I ⋙ k.completePush A I ⋙
      ObjectProperty.ι (Y'.IsComplete A I)).obj K) ≅
    ((ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
      h.towerPull A ⋙ k.towerPush A ⋙ Y'.rlim A).obj K) :=
  (k.directLimitIso A).app ((X'.reduction A I).obj ((h.pull A).obj K.obj)) ≪≫
    (Y'.rlim A).mapIso ((k.towerPush A).mapIso ((h.reductionPullIso A I).symm.app K.obj))

/-- Naturality of the specified t components.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison).
Proof: directLimitIso and reductionPullIso are natural isomorphisms. Their
whiskerings and composite remain natural; restrict this equality to complete inputs. -/
theorem comparisonT_naturality {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K L : X.Complete A I) (a : K ⟶ L) :
    (h.completePull A I ⋙ k.completePush A I ⋙
        ObjectProperty.ι (Y'.IsComplete A I)).map a ≫
        (comparisonTComponent (h := h) (k := k) A I L).hom =
      (comparisonTComponent (h := h) (k := k) A I K).hom ≫
        (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
          h.towerPull A ⋙ k.towerPush A ⋙ Y'.rlim A).map a := by
  exact ((Functor.whiskerLeft (h.pull A ⋙ X'.reduction A I)
    (k.directLimitIso A).hom) ≫ Functor.whiskerRight (h.reductionPullIso A I).inv
      (k.towerPush A ⋙ Y'.rlim A)).naturality a.hom

/-- The specified natural direct-image/limit comparison t.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison). -/
def comparisonT {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    h.completePull A I ⋙ k.completePush A I ⋙ ObjectProperty.ι (Y'.IsComplete A I) ≅
      ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
        h.towerPull A ⋙ k.towerPush A ⋙ Y'.rlim A :=
  NatIso.ofComponents (comparisonTComponent A I)
    (fun a ↦ comparisonT_naturality A I _ _ a)

/-- The whole-diagram mate comparison, including invertibility and the two finite
coefficient normalization clauses.

Source: smooth-purity blueprint, proposition-composition-base-change-rf-shriek Proof Step 4;
ingredient sources Stacks 099M, 099N, 0E48, 0941, 0B56, 0944
(blueprint: lem-sp-completion-mate-comparison).

Proof, following the ten steps of the DAG node:
1. Realize the strict sequence category on the diagram site. Use one flat-term
K-flat model for K and tensor it with the whole strict quotient diagram; its diagonal
is K-flat by levelwise acyclicity. This identifies the reduction/pullback comparisons.
2. The constant-tower functor preserves K-injectives, since evaluation at its terminal
index is exact and left adjoint to it. Its derived units and counits are the ordinary
ones termwise. The derived quotient augmentation therefore gives exactly the fixed
completion unit.
3. Evaluation of the strict projection adjunct gives finiteProjection. Each quotient
is perfect, hence has a bounded finite-projective model. Constant sheafification and
inverse image preserve its finite-free retracts. The finite total projection formula
makes every evaluated projection invertible; levelwise cohomology detects its cone.
Thus H is invertible and has the stated finite evaluation.
4. The identity-component constant/pullback square gives directLimitIso by adjunction
conjugation. On a K-injective strict tower it is the ordinary direct-image/limit map;
its projections are the direct images of the tower projections. This is t.
5. Apply ringedExchangeTensorCoherence on the diagram sites with the diagonal of K
and the whole quotient diagram. The diagram exchange on the diagonal is the diagonal
of the ordinary mate. The resulting equality holds before any evaluation or limit.
6. Naturality of the projection adjunct in the coefficient, and its tensor-unit
normalization, identify its composition with the quotient augmentation with direct
image of that augmentation. Apply total derived limit to obtain the corresponding
completion-unit equation.
7. The strict expression t inverse followed by limit(v) followed by s extends the
ordinary mate followed by the completed target unit. Completeness of that target
and direct-image preservation give uniqueness of this extension.
8. For each pair of edges, transpose under the ordinary and completion adjunctions.
The comparison C(v^* unit) is invertible by reflection and preservation of complete
objects under direct image. This calculation identifies the completed pullback square
with the conjugate of the prescribed right-adjoint square, including units and counits.
9. Transpose the completed mate and precompose with the completion unit. The triangle
identities give the same extension as in step 7. Uniqueness proves the displayed
natural-transformation equality, not merely equality of evaluated tower maps.
10. Evaluate the strict derived adjunction on a K-injective tower and use its exact
left adjoint. Finite scalar restriction commutes with direct image by adjunction
conjugation and with inverse image on generalized sections. These comparisons turn
the evaluated tower mate into ordinaryExchange over the original quotient ring.
No properness, smoothness, constructibility, boundedness or etale-origin condition
is used. Empty sites, the zero ideal and the unit ideal are included. -/
theorem completionMateComparison
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (_hperfect : PerfectQuotients A I) :
    (∀ K : X.Complete A I,
      IsIso (projectionComparison (f := f) (g := g) A I K.obj)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map (projectionComparison (f := f) (g := g) A I K.obj) ≫
          (finiteSourceIso (f := f) (g := g) A I n K.obj).hom =
        (Y'.finiteEvaluationIso A I n).hom.app ((g.pull A).obj ((f.push A).obj K.obj)) ≫
          (Y'.finiteRestriction A I n).map
            (finiteProjectionComparison (f := f) (g := g) A I n K.obj)) ∧
    (Functor.whiskerRight (completeExchange sq A I) (ObjectProperty.ι (Y'.IsComplete A I)) ≫
        (comparisonT (h := h) (k := k) A I).hom =
      comparisonS (f := f) (g := g) A I ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I)
            (towerExchange sq A)) (Y'.rlim A)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map ((towerExchange sq A).app ((X.reduction A I).obj K.obj)) ≫
          (finiteTargetIso (h := h) (k := k) A I n K.obj).hom =
        (finiteSourceIso (f := f) (g := g) A I n K.obj).hom ≫
          (Y'.finiteRestriction A I n).map
            ((ordinaryExchange sq (quotientRing A I n)).app
              ((X.finiteReduction A I n).obj K.obj))) := by
  sorry

end CategoryTheory.AdicSites
