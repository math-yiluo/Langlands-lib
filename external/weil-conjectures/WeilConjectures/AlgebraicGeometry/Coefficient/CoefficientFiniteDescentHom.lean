/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
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
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
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
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
public import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
public import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
public import Mathlib.Data.Matrix.Basic
public import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
public import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
public import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
public import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
public import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
public import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement
public import WeilConjectures.CategoryTheory.DirectedTriangulatedImage
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationDescent
public import WeilConjectures.AlgebraicGeometry.CondensedLfpCoefficientModel
public import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationMatrices
public import WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocalModelGluing
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubmoduleGluing
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubmoduleGluingData
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubsheafGluing
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernelEffective
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalQuotientVanishing
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteLocalSubmodules
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFamilyHomDescent
public import WeilConjectures.AlgebraicGeometry.CondensedLocalCoefficientAdjoints
public import WeilConjectures.AlgebraicGeometry.CondensedOverlapFactorTranspose
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.CondensedFpHomStage
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelAssembly
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStep
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonempty
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyOpenClosed
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyOpenPiece
public import WeilConjectures.Topology.StratificationDense
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteModelImmersionRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CondensedLocalPresentationPullback
public import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyComplement
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepNonemptyGluing
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteModelExtensions
public import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
public import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
public import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Data.Int.Interval
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
public import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.GradedObject.Bifunctor
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.GradedObject.Trifunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Geometry.RingedSpace.PresheafedSpace
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Topology.Category.CompHausLike.Basic
public import Mathlib.Topology.Category.CompHausLike.Limits
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Category.Profinite.Limits
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.ContinuousMap.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleOneStep
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexPresentation
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexModel
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexCompatibility
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteCoefficientLocalization
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleOpenClosedImages
public import WeilConjectures.AlgebraicGeometry.CondensedStratumModelInductionStepEmpty

/-!
# Finite descent of derived coefficient morphisms

Source: blueprint main-20261015, chap-Construction-of-f,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md and its proof
(blueprint: lemma-descent-finite-coefficient-field--1).

All coefficient maps, adjunctions, and tensor comparisons below are the recorded
constructions. The Hom-colimit assertion is expressed by surjectivity on finite
representatives and equality after passing to a common finite field.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u vA uA vB uB vC uC vZ uZ

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- Transport a shifted morphism by scalar extension and the given canonical tensor
comparison. Source: blueprint coefficient-finite-descent-hom, proof paragraph (1),
tensor transitivity (blueprint: lemma-descent-finite-coefficient-field--1). -/
def coefficientDescentDerivedHomMap
    {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {T : A ⥤ B} (S : B ⥤ V) [S.CommShift ℤ] {W : A ⥤ V}
    (α : T ⋙ S ≅ W) (C D : A) (r : ℤ)
    (f : T.obj C ⟶ (T.obj D)⟦r⟧) : W.obj C ⟶ (W.obj D)⟦r⟧ :=
  α.inv.app C ≫ S.map f ≫ (S.commShiftIso r).hom.app (T.obj D) ≫
    (α.hom.app D)⟦r⟧'

/-- The coefficient-inclusion map on restricted extensions is the adjunction mate
of tensor transitivity and the old counit. This fixes the actual transition map.
Source: blueprint coefficient-finite-descent-hom, proof paragraph (1), unit and counit
formulas (blueprint: lemma-descent-finite-coefficient-field--1). -/
def coefficientDescentDerivedRestrictionMap
    {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {T : A ⥤ B} {U : B ⥤ A} (a : T ⊣ U)
    (S : B ⥤ V) [S.CommShift ℤ]
    {W : A ⥤ V} {Z : V ⥤ A} (b : W ⊣ Z) (α : T ⋙ S ≅ W)
    (D : A) (r : ℤ) : U.obj ((T.obj D)⟦r⟧) ⟶ Z.obj ((W.obj D)⟦r⟧) :=
  b.homEquiv _ _
    (α.inv.app _ ≫ S.map (a.counit.app ((T.obj D)⟦r⟧)) ≫
      (S.commShiftIso r).hom.app (T.obj D) ≫ (α.hom.app D)⟦r⟧')

private theorem descentHomMap_comp {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {Z : Type uZ} [Category.{vZ} Z] [HasShift Z ℤ]
    {T : A ⥤ B} (U : B ⥤ V) [U.CommShift ℤ]
    (S : V ⥤ Z) [S.CommShift ℤ]
    {W : A ⥤ V} {R : B ⥤ Z} [R.CommShift ℤ] {Q : A ⥤ Z}
    (α : T ⋙ U ≅ W) (β : U ⋙ S ≅ R) [NatTrans.CommShift β.hom ℤ]
    (γ : W ⋙ S ≅ Q) (δ : T ⋙ R ≅ Q)
    (hc : ∀ M, S.map (α.hom.app M) ≫ γ.hom.app M =
      β.hom.app (T.obj M) ≫ δ.hom.app M)
    (C D : A) (r : ℤ) (f : T.obj C ⟶ (T.obj D)⟦r⟧) :
    coefficientDescentDerivedHomMap S γ C D r
      (coefficientDescentDerivedHomMap U α C D r f) =
        coefficientDescentDerivedHomMap R δ C D r f := by
  have hs (M : A) : γ.inv.app M ≫ S.map (α.inv.app M) =
      δ.inv.app M ≫ β.inv.app (T.obj M) := by
    apply (cancel_mono (S.map (α.hom.app M) ≫ γ.hom.app M)).mp
    simp only [Category.assoc, ← S.map_comp_assoc, Iso.inv_hom_id_app,
      Iso.inv_hom_id_app]
    rw [hc]
    simp
  dsimp only [coefficientDescentDerivedHomMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  rw [S.commShiftIso_hom_naturality_assoc]
  have hb := NatTrans.shift_app_comm β.hom r (T.obj D)
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  rw [← (shiftFunctor Z r).map_comp, hc, (shiftFunctor Z r).map_comp]
  rw [reassoc_of% hb]
  have hn := β.hom.naturality f
  change S.map (U.map f) ≫ β.hom.app _ = β.hom.app _ ≫ R.map f at hn
  rw [reassoc_of% hn]
  simp

private theorem adjunction_comparison_naturality {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] {V : Type uC} [Category.{vC} V]
    {T : A ⥤ B} {U : B ⥤ A} (a : T ⊣ U) (S : B ⥤ V)
    {W : A ⥤ V} {Z : V ⥤ A} (b : W ⊣ Z) (α : T ⋙ S ≅ W)
    (C : A) (Y : B) (Y' : V) (f : T.obj C ⟶ Y) (q : S.obj Y ⟶ Y') :
    b.homEquiv C Y' (α.inv.app C ≫ S.map f ≫ q) =
      a.homEquiv C Y f ≫ b.homEquiv (U.obj Y) Y'
        (α.inv.app (U.obj Y) ≫ S.map (a.counit.app Y) ≫ q) := by
  rw [← b.homEquiv_naturality_left]
  congr 1
  rw [α.inv.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← S.map_comp_assoc]
  have hh := (a.homEquiv C Y).symm_apply_apply f
  rw [a.homEquiv_counit] at hh
  rw [hh]

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The specified finite-field extension map on shifted derived Hom.
Source: blueprint coefficient-finite-descent-hom, clauses (1) and (3)
(blueprint: lemma-descent-finite-coefficient-field--1). -/
def coefficientDescentHomTransition
    {E F G : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (k : F ≤ G)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ)
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    (derivedExtendScalarsSubfield X ℓ (h.trans k)).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ (h.trans k)).obj D)⟦r⟧ :=
  coefficientDescentDerivedHomMap (derivedExtendScalarsSubfield X ℓ k)
    (condensedCoefficientCompIso X ℓ h k) C D r f

/-- The specified extension-to-algebraic-closure map on shifted derived Hom.
Source: blueprint coefficient-finite-descent-hom, clauses (1) and (3)
(blueprint: lemma-descent-finite-coefficient-field--1). -/
def coefficientDescentHomToAlgCl
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ)
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C ⟶
      ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D)⟦r⟧ :=
  coefficientDescentDerivedHomMap (derivedExtendScalarsToPadicAlgCl X ℓ F)
    (derivedExtendScalarsCompIso X ℓ h) C D r f

/-- The finite-stage transition on restricted shifted derived extensions.
Source: blueprint coefficient-finite-descent-hom, clause (1), transition identity
(blueprint: lemma-descent-finite-coefficient-field--1). -/
def coefficientDescentRestrictionTransition
    {E F G : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (k : F ≤ G)
    (D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) :
    (finiteCoefficientDerivedRestriction X ℓ h).obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) ⟶
      (finiteCoefficientDerivedRestriction X ℓ (h.trans k)).obj
        (((derivedExtendScalarsSubfield X ℓ (h.trans k)).obj D)⟦r⟧) :=
  coefficientDescentDerivedRestrictionMap (finiteCoefficientDerivedAdjunction X ℓ h)
    (derivedExtendScalarsSubfield X ℓ k)
    (finiteCoefficientDerivedAdjunction X ℓ (h.trans k))
    (condensedCoefficientCompIso X ℓ h k) D r

/-- The algebraic-closure transition on restricted shifted derived extensions.
Source: blueprint coefficient-finite-descent-hom, clause (1), transition identity
(blueprint: lemma-descent-finite-coefficient-field--1). -/
def coefficientDescentRestrictionToAlgCl
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) :
    (finiteCoefficientDerivedRestriction X ℓ h).obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) ⟶
      (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
        (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D)⟦r⟧) :=
  coefficientDescentDerivedRestrictionMap (finiteCoefficientDerivedAdjunction X ℓ h)
    (derivedExtendScalarsToPadicAlgCl X ℓ F)
    (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
    (derivedExtendScalarsCompIso X ℓ h) D r

/-- The poset of finite fields containing E, lifted to the coefficient universe.
Source: blueprint coefficient-finite-descent-hom, proof paragraph (2)
(blueprint: lemma-descent-finite-coefficient-field--1). -/
def coefficientDescentFields (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
  (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E

private lemma constructibleToPadicAlgCl_map_hom (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K L : PadicSubfieldConstructible X ℓ E} (f : K ⟶ L) :
    ((constructibleToPadicAlgCl X ℓ E).map f).hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map f.hom := rfl

private lemma tensorComp_hom {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).hom.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  exact Category.id_comp _

private lemma tensorComp_inv {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).inv.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).inv.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.refl_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.comp_id]
  rfl

private lemma tensorCompShift {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    NatTrans.CommShift (finiteCoefficientDerivedTensorCompIso X ℓ h).hom ℤ := by
  exact Functor.leftComp_shift
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F))
    ((Mod.extendScalarsComp _ _).symm ≪≫
      Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))

private lemma descentHomToAlgCl_transition [TopologicalSpace.NoetherianSpace X]
    {E F G : FiniteIntermediateField ℓ} (h : E ≤ F) (j : F ≤ G)
    (C D : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    coefficientDescentHomToAlgCl X ℓ (h.trans j) C D r
      (coefficientDescentHomTransition X ℓ h j C D r f) =
        coefficientDescentHomToAlgCl X ℓ h C D r f := by
  let : NatTrans.CommShift (derivedExtendScalarsCompIso X ℓ j).hom ℤ :=
    tensorCompShift X ℓ j
  exact descentHomMap_comp (derivedExtendScalarsSubfield X ℓ j)
    (derivedExtendScalarsToPadicAlgCl X ℓ G)
    (condensedCoefficientCompIso X ℓ h j) (derivedExtendScalarsCompIso X ℓ j)
    (derivedExtendScalarsCompIso X ℓ (h.trans j)) (derivedExtendScalarsCompIso X ℓ h)
    (fun M ↦ by
      have hc := congr_app (congrArg Iso.hom
        ((condensedCoefficientCoherence X ℓ).2.1 E F G h j)) M
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.id_comp] using hc) C D r f

set_option backward.isDefEq.respectTransparency true in
private lemma descentHomToAlgCl_injective
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (C D : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) : Function.Injective (coefficientDescentHomToAlgCl X ℓ h C D r) := by
  let : (derivedExtendScalarsToPadicAlgCl X ℓ F).Faithful :=
    faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ F
  intro f g e
  dsimp only [coefficientDescentHomToAlgCl, coefficientDescentDerivedHomMap] at e
  apply (derivedExtendScalarsToPadicAlgCl X ℓ F).map_injective
  have e' := (cancel_epi ((derivedExtendScalarsCompIso X ℓ h).inv.app C)).mp e
  simpa only [← Category.assoc, cancel_mono] using e'

/-- Derived coefficient Hom adjunction, its coefficient naturality, the uniformly
bounded-below coefficient tensor colimit, and bijectivity on finite representatives.
Source: blueprint main-20261015, lemma-descent-finite-coefficient-field,
sk-lem-coefficient-finite-descent-hom.md, clauses (1)--(3)
(blueprint: lemma-descent-finite-coefficient-field--1).

Proof, following the ten DAG steps:
1. On a small skeleton of the pro-etale site, sheaf tensor is closed and preserves
colimits (lemma-descent-finite-coefficient-field--1). The extension/restriction adjunction of
lemma-descent-finite-coefficient-field--1 has exact restriction; prose-03-27 and
prose-03-27 make extension exact as well.
2. Lift this adjunction to complexes by lemma-descent-finite-coefficient-field--1.
Exact functors preserve quasi-isomorphisms by
situation-conventions. Apply lemma-descent-finite-coefficient-field--1:
the Hom map is restriction followed by the unit, and its inverse is extension
followed by the counit. Restriction commutes with shifts.
3. Identify the recorded left-derived extensions with these termwise extensions
by the exact-functor clause of lemma-descent-finite-coefficient-field--1.
4. Tensor multiplication and insertion of 1 give inverse transitivity maps.
Their unit compatibility and situation-conventions identify
them with definition-sp-scalar-extension--2 and the recorded finite comparison.
5. The inclusion map sends the old unit to the new one. Counit naturality gives
the two displayed Hom-naturality identities, also for the algebraic closure.
6. The finite fields containing E form a nonempty directed poset, by finite
composita (prose-02-50). The ring cocone of
lemma-comparison-completed-coefficients remains colimiting on this tail: extend a cocone on
the tail to every finite H via EH. All legs remain the actual inclusions.
7. Use lemma-descent-finite-coefficient-field--1 and
lemma-descent-finite-coefficient-field--1 to identify this same cocone as a
colimit of E-module sheaves.
8. Tensor with each term of the representative preserves this colimit, by
lemma-descent-finite-coefficient-field--1; its balancing maps are those of
prose-03-02. The comparisons commute with differentials.
Additivity preserves every zero term below the given lower bound.
9. The standing scheme is Noetherian by lemma-descent-finite-coefficient-field--1.
Bounded constructibility and lemma-descent-finite-coefficient-field--1 give a bounded
representative of D.
10. Apply lemma-continuity-ext-out-constructible-complex--1 with source C, the coefficient
diagram of steps 6--8, and degree r. The identities of step 5 identify its
comparison with coefficient extension on Hom. A filtered-colimit element is a
finite representative, and equality is equality at a common later stage. Thus
the last two clauses say exactly that this canonical comparison is bijective.
-/
theorem coefficient_finite_descent_hom
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) :
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      Function.Bijective (finiteCoefficientDerivedHomEquiv X ℓ h C.obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧))) ∧
    Function.Bijective (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj
      (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧)) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : F ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedHomEquiv X ℓ (h.trans j) C.obj _
          (coefficientDescentHomTransition X ℓ h j C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionTransition X ℓ h j D.obj r) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _
          (coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionToAlgCl X ℓ h D.obj r) ∧
    (∀ (K : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ℤ)
      (_e : DerivedCategory.Q.obj K ≅ D.obj) (a b : ℤ)
      (_hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)),
      IsFiltered (AsSmall.{u + 1} (Under E)) ∧
        Nonempty (IsColimit (coefficientComplexCocone X ℓ K (coefficientDescentFields ℓ E)
          (fun i => leOfHom (ULift.down i).hom) (fun i => leOfHom (ULift.down i).hom))) ∧
        ∀ (i : AsSmall.{u + 1} (Under E)) (n : ℤ), n < a →
          IsZero (((coefficientComplexDiagram X ℓ K (coefficientDescentFields ℓ E)
            (fun j => leOfHom (ULift.down j).hom)
            (fun j => leOfHom (ULift.down j).hom)).obj i).X n)) ∧
    (∀ f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (g : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
        coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r g = f) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : E ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧)
      (g : (derivedExtendScalarsSubfield X ℓ j).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ j).obj D.obj)⟦r⟧),
      coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f =
        coefficientDescentHomToAlgCl X ℓ j C.obj D.obj r g →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (hF : F ≤ H) (hG : G ≤ H),
        coefficientDescentHomTransition X ℓ h hF C.obj D.obj r f =
          coefficientDescentHomTransition X ℓ j hG C.obj D.obj r g) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F h
    exact (finiteCoefficientDerivedHomEquiv X ℓ h C.obj _).bijective
  · exact (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _).bijective
  · intro F G h j f
    exact adjunction_comparison_naturality
      (finiteCoefficientDerivedAdjunction X ℓ h)
      (derivedExtendScalarsSubfield X ℓ j)
      (finiteCoefficientDerivedAdjunction X ℓ (h.trans j))
      (condensedCoefficientCompIso X ℓ h j) C.obj _ _ f _
  · intro F h f
    exact adjunction_comparison_naturality
      (finiteCoefficientDerivedAdjunction X ℓ h)
      (derivedExtendScalarsToPadicAlgCl X ℓ F)
      (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
      (derivedExtendScalarsCompIso X ℓ h) C.obj _ _ f _
  · intro K e a b hK
    let : (coefficientDescentFields ℓ E).Final := by
      dsimp [coefficientDescentFields]
      infer_instance
    refine ⟨?_, ?_, ?_⟩
    · exact IsFiltered.of_equivalence (AsSmall.equiv (C := Under E))
    · exact nonempty_isColimit_coefficientComplexCocone X ℓ K
        (coefficientDescentFields ℓ E) _ _
    · intro i n hn
      exact (Mod.comap (padicSubfieldRingObjMap X ℓ
        (leOfHom (ULift.down i).hom))).map_isZero
          ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ
            (leOfHom (ULift.down i).hom))).map_isZero (hK n (Or.inl hn)))
  · intro f
    have : (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated :=
      finiteBoundedTriangulated X ℓ E
    let D' : BoundedConstructible (padicSubfieldRingObj X ℓ E) :=
      ⟨D.obj⟦r⟧, (boundedConstructible (padicSubfieldRingObj X ℓ E)).le_shift r _ D.property⟩
    let f' := f ≫ ((derivedExtendScalarsToPadicAlgCl X ℓ E).commShiftIso r).inv.app D.obj
    obtain ⟨F, h, j, g, hg⟩ := constructibleCocone_homSurj X ℓ E E C D'
      (ObjectProperty.homMk f')
    let g' := g.hom ≫ ((derivedExtendScalarsSubfield X ℓ h).commShiftIso r).hom.app D.obj
    refine ⟨F, h, g', ?_⟩
    have hh := congrArg (·.hom) hg
    dsimp only [constructibleCocone] at hh
    simp only [ObjectProperty.FullSubcategory.comp_hom, tensorComp_inv, tensorComp_hom,
      constructibleToPadicAlgCl_map_hom] at hh
    have : NatTrans.CommShift (derivedExtendScalarsCompIso X ℓ h).hom ℤ :=
      tensorCompShift X ℓ h
    have hc := NatTrans.shift_app_comm (derivedExtendScalarsCompIso X ℓ h).hom r D.obj
    simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hc
    change f' = (derivedExtendScalarsCompIso X ℓ h).inv.app C.obj ≫
      (derivedExtendScalarsToPadicAlgCl X ℓ F).map g.hom ≫
        (derivedExtendScalarsCompIso X ℓ h).hom.app (D.obj⟦r⟧) at hh
    dsimp only [g', coefficientDescentHomToAlgCl, coefficientDescentDerivedHomMap]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    rw [← Category.assoc, ← Category.assoc]
    rw [← Category.assoc] at hh
    rw [← hh]
    simp only [f', Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id f
  · intro F G h j f g heq
    let H := IsFiltered.max F G
    have hF : F ≤ H := leOfHom (IsFiltered.leftToMax F G)
    have hG : G ≤ H := leOfHom (IsFiltered.rightToMax F G)
    refine ⟨H, hF, hG, ?_⟩
    apply descentHomToAlgCl_injective X ℓ (h.trans hF) C.obj D.obj r
    rw [descentHomToAlgCl_transition, descentHomToAlgCl_transition]
    exact heq

end AlgebraicGeometry.ProEtale
