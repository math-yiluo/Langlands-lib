/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperConstructibleHeartBound
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationContinuity
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralStratum
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import WeilConjectures.CategoryTheory.HomColimitExtension
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.HomColimitTruncation
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Topology.StratificationDense
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Grp.Adjunctions
import WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ContinuousLisseStratifiedLattices
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoversTop.Over
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.LargeSetSheafification
import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport
import WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeFiniteCoproductSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionLocalModel
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitData
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralLocalizationSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.CondensedUnderivedPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeKernelModel
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.AlgebraicGeometry.IntegralMatrixKernelLocallyFree
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects
import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-!
# Proper direct-image bound for rational constructible module sheaves

The two statements are the finite rational and algebraic-closure coefficient cases.
The integer dimension bound uses bottom for negative integers, since every nonempty
space has nonnegative Krull dimension. Thus negative bounds retain the empty-fibre case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CondensedRing

-- Keep scalar extension abstract while comparing coefficient-module functors.
attribute [local irreducible] Mod.extendScalars
  Functor.leftDerivedFunctorIsoMapDerivedCategory Functor.CommShift.ofIso
  Functor.mapDerivedCategorySingleFunctor CondensedRing.derivedComapLowerStarIso
  Mod.extendRestrictAdjunction
  CondensedRing.lowerStar Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem source_empty_of_geometric_fibers_empty
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ ⊥) : IsEmpty X := by
  refine ⟨fun x ↦ ?_⟩
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField (p x)) (AlgebraicClosure (Y.residueField (p x))))) ≫
      Y.fromSpecResidueField (p x)
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := g) x
    (IsLocalRing.closedPoint (AlgebraicClosure (Y.residueField (p x)))) (by
      exact (Y.fromSpecResidueField_apply (p x) _).symm)
  have he : IsEmpty (TopologicalSpace.IrreducibleCloseds (pullback p g : Scheme.{u})) :=
    Order.krullDim_eq_bot_iff.mp (le_antisymm (hd (p x)) bot_le)
  exact he.false ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩

private theorem module_zero_of_empty {X : Scheme.{u}} [IsEmpty X]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : IsZero M := by
  have hX : IsZero M.X := by
    apply Sheaf.isZero_of_isZero_obj
    rintro ⟨T⟩
    have : IsEmpty T.left := ⟨fun t ↦ (inferInstance : IsEmpty X).false (T.hom t)⟩
    exact (isZero_zero _).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X T).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  exact (IsZero.iff_id_eq_zero _).2 (Mod.hom_ext _ _ (hX.eq_of_src _ _))

private theorem localization_preserves_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.plus K) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (integralCoeff ℓ E) p).rightDerivedFunctor.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        ((integralScalarExtension ℓ E X).obj K))) := by
  let U : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y) :=
    Mod.comap (coefficientMap (integralScalarMap ℓ E) Y)
  apply U.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  have e := (derivedComapLowerStarIso (integralScalarMap ℓ E) p).app
    ((integralScalarExtension ℓ E X).obj K)
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ q).mapIso e)
  obtain ⟨hc⟩ := integralLocalization_push_homology_isColimit ℓ E p K hK q
  apply (IsZero.iff_id_eq_zero _).2
  apply hc.hom_ext
  intro i
  exact hq.eq_of_src _ _

private theorem qbar_scalar_preserves_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (q : ℤ) (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N)))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N)))) := by
  classical
  obtain ⟨I, b, _, _, hcopower⟩ := exists_condensedQbar_scalar_basis_sections.{u} ℓ E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasColimitsOfSize.{u + 1, u + 1} B := IsGrothendieckAbelian.hasColimits B
  let : HasCoproducts.{u + 1} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let : HasCoproducts.{u + 1} B := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let : HasCoproducts.{u + 1} (DerivedCategory A) := derived_hasCoproducts
  let : HasCoproducts.{u + 1} (DerivedCategory B) := derived_hasCoproducts
  let F := (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor
  let T := DerivedCategory.singleFunctor A 0 ⋙ F ⋙ DerivedCategory.homologyFunctor B q
  let : PreservesColimit (Discrete.functor
      ((DerivedCategory.singleFunctor A 0).obj ∘ (fun _ : I ↦ N))) F :=
    condensed_boundedBelow_preservesCoproduct (Profinite.continuousMapRingObj E) p I 0
      (fun _ ↦ (DerivedCategory.singleFunctor A 0).obj N) (fun _ ↦ inferInstance)
  have : PreservesColimit (Discrete.functor (fun _ : I ↦ N) ⋙
      DerivedCategory.singleFunctor A 0) F :=
    preservesColimit_of_iso_diagram F (Discrete.compNatIsoDiscrete
      (fun _ : I ↦ N) (DerivedCategory.singleFunctor A 0)).symm
  have hz : IsZero (T.obj (∐ fun _ : I ↦ N)) := by
    apply (isColimitOfPreserves T (coproductIsCoproduct (fun _ : I ↦ N))).isZero_pt
    apply (CategoryTheory.Functor.isZero_iff _).mpr
    intro i
    exact hq
  have hi := hcopower X N
  -- Reuse the certified map, avoiding reconstruction of its scalar-action formula.
  let e := @asIso _ _ _ _ _ hi
  have he := hz.of_iso (T.mapIso e).symm
  let U : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClRingObj Y ℓ) ⥤ B :=
    Mod.comap (padicSubfieldRingObjToPadicAlgCl Y ℓ E)
  apply U.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  let K := (DerivedCategory.singleFunctor _ 0).obj
    ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N)
  let UX : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ) ⥤ A :=
    Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let es := (UX.mapDerivedCategorySingleFunctor 0).app
    ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N)
  let ep := (derivedComapLowerStarIso
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p).app K
  exact he.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    (ep ≪≫ F.mapIso es))

/-- The rational proper direct-image bound over a Noetherian source, with no base field. -/
theorem isZero_higherDirectImage_rational_of_isProper_of_isNoetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))
    (hM : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : NormedField E := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  by_cases hn : d < 0
  · let : IsEmpty X := source_empty_of_geometric_fibers_empty p (fun y ↦ by
      simpa only [ite_eq_left hn] using hd y)
    exact ((DerivedCategory.singleFunctor _ 0 ⋙
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q).map_isZero (module_zero_of_empty _ M))
  have hd' (y : Y) : topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d.toNat : WithBot ℕ∞) := by
    simpa only [ite_eq_right hn] using hd y
  -- Glue ordinary integral models, then reuse the integral completeness/torsion/Milnor bound.
  have hM' := ((adicConstructibilityPredicateComparison ℓ X
    (Profinite.continuousMapRingObj E) (.continuous E)).1 M).mpr hM
  obtain ⟨S, hS⟩ := hM'
  have hmodels := fun a ↦ continuousConstructible_integral_stratum ℓ E X
    (S.immersion a) _ (hS a)
  obtain ⟨N, hN, ⟨eN⟩⟩ := continuousConstructible_integral_gluing ℓ E X M S hmodels
  have hN' : IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X N :=
    ((adicConstructibilityPredicateComparison ℓ X
      (Profinite.padicIntegersRingObj ℓ E) (.integral E)).1 N).mp hN
  have hb := integralProperConstructibleHeartBound_of_isNoetherian ℓ E p d.toNat hd' N hN'
  have hv := DerivedCategory.isZero_of_isLE _ (2 * (d.toNat : ℤ) + 1) q
    (by omega) (hX := hb)
  -- The localization unit telescope transfers the same bound to E coefficients.
  have hl := localization_preserves_vanishing ℓ E p
    ((DerivedCategory.singleFunctor _ 0).obj N) (by
      exact ⟨0, inferInstance⟩) q hv
  let e := (Functor.singleFunctorCompLeftDerivedFunctorIso
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))).app N ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eN
  exact hl.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.mapIso
      e)).symm

set_option linter.unusedVariables false in
/-- The proper direct-image bound for a finite subextension of Qbar_ell. -/
theorem isZero_higherDirectImage_rational_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (k : Type u) [Field k]
    (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))
    (hM : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  exact isZero_higherDirectImage_rational_of_isProper_of_isNoetherian ℓ E p d hd M hM q hq

/-- The algebraic-closure proper direct-image bound over a Noetherian source, with no base
field. -/
theorem isZero_higherDirectImage_padicAlgCl_of_isProper_of_isNoetherian
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have hcomp := adicConstructibilityPredicateComparison ℓ X
    (Profinite.padicAlgClRingObj ℓ) .algebraicClosure
  have hm := (hcomp.1 M).mpr hM
  let K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj M, by
      rw [← hcomp.2]
      refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · exact isConstructibleModuleObject_of_isZero _
          (DerivedCategory.isZero_of_isGE _ 0 n hn)
      · exact IsConstructibleModuleObject.of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hm
      · exact isConstructibleModuleObject_of_isZero _
          (DerivedCategory.isZero_of_isLE _ 0 n hn)⟩
  -- Exact finite-coefficient descent of M[0] gives an ordinary model after taking H⁰.
  obtain ⟨E, L, ⟨eL⟩⟩ :=
    (coefficient_finite_descent_objects_of_isNoetherian ℓ X).1 K
  let N := (DerivedCategory.homologyFunctor _ 0).obj L.obj
  have hN : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N :=
    L.property.2 0
  let eN : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N ≅ M :=
    (Functor.leftDerivedFunctorHomologyFunctorIso
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) 0).app L.obj ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso eL ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M
  have hz := qbar_scalar_preserves_vanishing ℓ E p N q
    (isZero_higherDirectImage_rational_of_isProper_of_isNoetherian ℓ E p d hd N hN q hq)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso eN))).symm

set_option linter.unusedVariables false in
/-- The proper direct-image bound for the finite-subextension-valued condensed ring Qbar_ell. -/
theorem isZero_higherDirectImage_padicAlgCl_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  exact isZero_higherDirectImage_padicAlgCl_of_isProper_of_isNoetherian ℓ p d hd M hM q hq

end AlgebraicGeometry.ProEtale
