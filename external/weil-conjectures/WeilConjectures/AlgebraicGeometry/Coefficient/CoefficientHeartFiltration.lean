/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Subobject.Lattice
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedReconstruction
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.Algebra.Category.Ring.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Order.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all WeilConjectures.ConstructibleSheaf.FreeLifting
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import all Mathlib.Topology.MetricSpace.Ultra.Basic
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Analysis.Normed.Group.Ultra
import all Mathlib.Data.Finset.Max
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all Mathlib.Algebra.Field.ULift
import all WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import all WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all Mathlib.Data.Fin.Tuple.Basic
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import all WeilConjectures.CategoryTheory.HomColimitExtension
import all Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.Algebra.Category.Grp.Colimits
import all Mathlib.CategoryTheory.Filtered.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.CategoryTheory.Triangulated.Yoneda
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import all Mathlib.CategoryTheory.Category.ULift
import all WeilConjectures.CategoryTheory.HomColimitTruncation
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all Mathlib.Algebra.Homology.QuasiIso
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import all WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.Topology.StratificationDense
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import all WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import all WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import all WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import all WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import all Mathlib.CategoryTheory.Sites.Adjunction
import all Mathlib.Algebra.Category.Grp.Adjunctions
import all WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# The filtration associated to an adapted coefficient stratification

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart/
sk-lem-coefficient-heart-filtration.md and its proof
(blueprint: lemma-constructible-sheaves--7).

The filtration steps are the images of the actual open-extension counits. The theorem
asserts that those counits are monomorphisms, so the images represent exactly the given
extensions by zero as subsheaves of F. Locally closed extension is the open extension
into the scheme-theoretic closure followed by its closed direct image.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The specified object `v_! v^* F` for an open subscheme V.
Source: blueprint sk-lem-coefficient-heart-filtration, definition of F_k
(blueprint: lemma-constructible-sheaves--7). -/
abbrev coefficientHeartOpenTerm {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) :=
  (CondensedRing.openImmersionLowerShriek Λ V.ι).obj
    ((CondensedRing.upperStar Λ V.ι).obj F)

/-- The canonical map from the open-extension term to F, namely the adjunction counit.
Source: blueprint sk-lem-coefficient-heart-filtration, definition of the inclusions
(blueprint: lemma-constructible-sheaves--7). -/
abbrev coefficientHeartOpenCounit {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) : coefficientHeartOpenTerm Λ F V ⟶ F :=
  (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ V.ι).counit.app F

/-- The subsheaf represented by the image of the canonical counit. Its equality with the
open-extension object as a subsheaf follows from the monomorphism assertion below.
Source: blueprint sk-lem-coefficient-heart-filtration, F_k as a subsheaf of F
(blueprint: lemma-constructible-sheaves--7). -/
abbrev coefficientHeartFiltrationStep {X : Scheme.{u}}
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : X.Opens) : Subobject F :=
  imageSubobject (coefficientHeartOpenCounit Λ F V)

/-- For a locally closed immersion a into a topologically Noetherian scheme, use its
canonical scheme-theoretic closure: `a.toImage` is open and `a.imageι` is closed.
The source is topologically Noetherian because an immersion is a topological embedding;
therefore a is quasi-compact and the existing open-immersion instance for `a.toImage`
applies. No choice of an extension functor is made.
Source: blueprint sk-lem-coefficient-heart-filtration, definition `a_! = i_* u_!`
(blueprint: lemma-constructible-sheaves--7). -/
def coefficientHeartLocallyClosedExtension {S X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (a : S ⟶ X) (ha : IsImmersion a) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  CondensedRing.openImmersionLowerShriek Λ a.toImage ⋙ CondensedRing.lowerStar Λ a.imageι

private theorem filtrationEssentiallySmall
    (C : Type (u + 1)) [CategoryTheory.Category.{u} C] :
    CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C
attribute [local instance 2000] filtrationEssentiallySmall

namespace CondensedRing

-- Use the earlier abelian support and module-transport interfaces directly. The
-- generator-tensor module containing analogous private wrappers imports this file.
attribute [local irreducible] upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction upperStar upperStarComp upperStarCongr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedOpen_to_closure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S V X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) [IsImmersion a]
    (t : S ⟶ V) [IsClosedImmersion t] (v : V ⟶ X) [IsOpenImmersion v]
    (htv : t ≫ v = a)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    Nonempty ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M) ≅
      (coefficientHeartLocallyClosedExtension Λ a inferInstance).obj M) := by
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian a.image := LocallyOfFiniteType.isLocallyNoetherian a.imageι
  have : TopologicalSpace.NoetherianSpace a.image :=
    a.imageι.isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian a.image := ⟨⟩
  let N := (openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M)
  have hs {Y : Scheme.{u}} (g : Y ⟶ X)
      (hg : Disjoint (Set.range g) (Set.range a)) :
      IsZero ((upperStar Λ g).obj N) := by
    have hdis : Disjoint (Set.range (pullback.snd g v)) (Set.range t) := by
      rw [Set.disjoint_left]
      rintro x ⟨y, rfl⟩ ⟨z, hz⟩
      apply Set.disjoint_left.mp hg
        (show v (pullback.snd g v y) ∈ Set.range g from
          ⟨pullback.fst g v y, by
            exact congrArg (fun f : pullback g v ⟶ X ↦ f y) pullback.condition⟩)
      exact ⟨z, (congrArg (fun f : S ⟶ X ↦ f z) htv).symm.trans (congrArg v hz)⟩
    let O : V.Opens := ⟨(Set.range t)ᶜ, t.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hO : Set.range O.ι = (Set.range t)ᶜ := O.range_ι
    have hfactor : Set.range (pullback.snd g v) ⊆ Set.range O.ι := by
      rw [hO]
      exact hdis.subset_compl_right
    let f := IsOpenImmersion.lift O.ι (pullback.snd g v) hfactor
    have hf : f ≫ O.ι = pullback.snd g v := IsOpenImmersion.lift_fac _ _ hfactor
    have hz := ((upperStar Λ f).map_isZero
      (openRestrictionPushforwardZero Λ t O.ι hO M)).of_iso
        ((upperStarCongr Λ hf.symm).app _ ≪≫ (upperStarComp Λ f O.ι).app _)
    have hz' := ((Mod.forget _).map_isZero hz).of_iso
      (upperStarObjXIso Λ (pullback.snd g v) _).symm
    have ebc := (ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1}
      (IsPullback.of_hasPullback g v).flip).app ((lowerStar Λ t).obj M).X
    exact isZero_of_isZero_X Λ
      (((ProEtale.openImmersionLowerShriek Ab.{u + 1} (pullback.fst g v)).map_isZero
        hz').of_iso (upperStarObjXIso Λ g _ ≪≫ ebc.symm))
  have hc : IsIso (upperStarLowerStarAdjunction Λ t).counit :=
    moduleCounitOfAbelian Λ t (ProEtale.abelian_closed_counit t)
  have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ v).unit :=
    openUnitIsIso Λ v
  let e : (upperStar Λ a).obj N ≅ M :=
    ((upperStarCongr Λ htv.symm).app N) ≪≫
      ((upperStarComp Λ t v).app N) ≪≫
      (upperStar Λ t).mapIso
        (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ v).unit.app
          ((lowerStar Λ t).obj M))).symm ≪≫
      asIso ((upperStarLowerStarAdjunction Λ t).counit.app M)
  let U : X.Opens :=
    ⟨(Set.range a.imageι)ᶜ, a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι = (Set.range a.imageι)ᶜ := by
    exact U.range_ι
  have houter : Disjoint (Set.range U.ι) (Set.range a) := by
    rw [hU, Set.disjoint_left]
    rintro x hx ⟨z, rfl⟩
    apply hx
    exact ⟨a.toImage z, (congrArg (fun f : S ⟶ X ↦ f z) a.toImage_imageι).symm⟩
  have houterAb := ((Mod.forget _).map_isZero (hs U.ι houter)).of_iso
    (upperStarObjXIso Λ U.ι N).symm
  have ho := moduleUnitOfAbelian Λ a.imageι N
    ((ProEtale.abelian_closed_support_counit_and_unit a.imageι U.ι hU).2 N.X houterAb)
  have hd : Disjoint (Set.range (a.toImage.closedComplement ≫ a.imageι))
      (Set.range a) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    have he : a.toImage z = a.toImage.closedComplement y :=
      a.imageι.isEmbedding.injective
        ((congrArg (fun f : S ⟶ X ↦ f z) a.toImage_imageι).trans hz)
    have hy : a.toImage.closedComplement y ∈ (Set.range a.toImage)ᶜ := by
      rw [← a.toImage.range_closedComplement]
      exact ⟨y, rfl⟩
    exact hy ⟨z, he⟩
  have hz := (hs (a.toImage.closedComplement ≫ a.imageι) hd).of_iso
    ((upperStarComp Λ a.toImage.closedComplement a.imageι).app N).symm
  have hzAb := ((Mod.forget _).map_isZero hz).of_iso
    (upperStarObjXIso Λ a.toImage.closedComplement _).symm
  have hopenAb := ProEtale.abelian_open_supported_counit
    a.toImage.closedComplement a.toImage
    (by rw [a.toImage.range_closedComplement, compl_compl])
    ((upperStar Λ a.imageι).obj N).X hzAb
  have hi : IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ a.toImage).counit.app
      ((upperStar Λ a.imageι).obj N)) := by
    apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
    apply mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ a.toImage
    exact (Adjunction.isIso_counit_app_iff_mem_essImage _).1 hopenAb
  refine ⟨asIso ((upperStarLowerStarAdjunction Λ a.imageι).unit.app N) ≪≫
    (lowerStar Λ a.imageι).mapIso
      (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ a.toImage).counit.app
        ((upperStar Λ a.imageι).obj N))).symm ≪≫ ?_⟩
  exact (lowerStar Λ a.imageι).mapIso ((openImmersionLowerShriek Λ a.toImage).mapIso
    (((upperStarComp Λ a.toImage a.imageι).symm ≪≫
      upperStarCongr Λ a.toImage_imageι).app N ≪≫ e))

end CondensedRing

attribute [local irreducible] CondensedRing.openImmersionLowerShriekUpperStarAdjunction
  CondensedRing.upperStarLowerStarAdjunction coefficientHeartLocallyClosedExtension
  CondensedRing.upperStar CondensedRing.openImmersionLowerShriek CondensedRing.lowerStar
  CondensedRing.upperStarComp CondensedRing.upperStarCongr

private theorem evaluated_cokernel
    {C D : Type*} [Category C] [Category D] [Abelian D]
    {P Q H : C ⥤ D} (d : P ⟶ Q) (e : cokernel d ≅ H) (F : C) :
    Nonempty (cokernel (d.app F) ≅ H.obj F) := by
  let ev := (evaluation C D).obj F
  exact ⟨(PreservesCokernel.iso ev d).symm ≪≫ e.app F⟩

-- Keep the representative transport abstract, so it does not unfold the scheme
-- pullback and open-extension definitions while transporting a dependent cokernel.
private theorem image_subobject_cokernel
    {C : Type*} [Category C] [Abelian C] {B A₁ A₂ : C}
    (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g]
    (d : A₁ ⟶ A₂) (hd : d ≫ g = f)
    (h : imageSubobject f ≤ imageSubobject g) :
    Nonempty (cokernel (Subobject.ofLE _ _ h) ≅ cokernel d) := by
  have aux (P Q : Subobject B) (hP : P = Subobject.mk f) (hQ : Q = Subobject.mk g)
      (hPQ : P ≤ Q) : Nonempty (cokernel (Subobject.ofLE P Q hPQ) ≅ cokernel d) := by
    subst P
    subst Q
    exact ⟨Subobject.cokernelOfLEMkIso f g (Iso.refl _) d (by simpa using hd.symm) hPQ⟩
  exact aux _ _ (imageSubobject_mono _) (imageSubobject_mono _) h

-- Work with the counits as variables when comparing their actual image subobjects.
private theorem successor_image_quotient
    {C : Type*} [Category C] [Abelian C] {P Q H : C ⥤ C}
    (εP : P ⟶ 𝟭 C) (εQ : Q ⟶ 𝟭 C)
    (hP : ∀ F, Mono (εP.app F)) (hQ : ∀ F, Mono (εQ.app F))
    (hs : ∃ d : P ⟶ Q, d ≫ εQ = εP ∧ Nonempty (cokernel d ≅ H)) (F : C) :
    ∃ h : imageSubobject (εP.app F) ≤ imageSubobject (εQ.app F),
      Nonempty (cokernel (Subobject.ofLE _ _ h) ≅ H.obj F) := by
  obtain ⟨d, hd, ⟨ed⟩⟩ := hs
  have := hP F
  have := hQ F
  have hdF : d.app F ≫ εQ.app F = εP.app F := congr_app hd F
  have h : imageSubobject (εP.app F) ≤ imageSubobject (εQ.app F) := by
    rw [imageSubobject_mono, imageSubobject_mono]
    exact Subobject.mk_le_mk_of_comm (d.app F) hdF
  refine ⟨h, ?_⟩
  obtain ⟨e⟩ := image_subobject_cokernel (εP.app F) (εQ.app F) (d.app F) hdF h
  obtain ⟨e'⟩ := evaluated_cokernel d ed F
  exact ⟨e ≪≫ e'⟩

-- The successor interface compares the actual chosen image subobjects and closure extension.
private theorem nestedOpen_quotient
    {X : Scheme.{u}} [IsNoetherian X] (W T : X.Opens) (hWT : W ≤ T)
    {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (t : S ⟶ T.toScheme) [IsClosedImmersion t] (htv : t ≫ T.ι = a)
    (ht : Set.range t = {x | T.ι x ∉ W})
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∃ h : coefficientHeartFiltrationStep Λ F W ≤ coefficientHeartFiltrationStep Λ F T,
      Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
        (coefficientHeartLocallyClosedExtension Λ a inferInstance).obj
          ((CondensedRing.upperStar Λ a).obj F)) := by
  classical
  obtain ⟨h, he⟩ := successor_image_quotient
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ W.ι).counit
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ T.ι).counit
    (CondensedRing.mono_condensed_counit Λ W.ι)
    (CondensedRing.mono_condensed_counit Λ T.ι)
    (CondensedRing.exists_openFiltrationSuccessor Λ W T hWT t ht) F
  refine ⟨h, ?_⟩
  obtain ⟨e⟩ := he
  let M := (CondensedRing.upperStar Λ a).obj F
  let er : (CondensedRing.upperStar Λ t).obj ((CondensedRing.upperStar Λ T.ι).obj F) ≅ M :=
    ((CondensedRing.upperStarComp Λ t T.ι).symm ≪≫
      CondensedRing.upperStarCongr Λ htv).app F
  obtain ⟨ec⟩ := CondensedRing.closedOpen_to_closure Λ a t T.ι htv M
  exact ⟨e ≪≫
    (CondensedRing.openImmersionLowerShriek Λ T.ι).mapIso
      ((CondensedRing.lowerStar Λ t).mapIso er) ≪≫ ec⟩

-- The filtration construction is independent of the coefficient-specific lisseness criterion.
private theorem openPrefix_filtration
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (R : X.FiniteLocallyClosedStratification)
    (V : Fin (R.n + 1) → X.Opens)
    (hV : ∀ k : Fin (R.n + 1),
      (V k : Set X) = ⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) :
    (∀ k : Fin (R.n + 1),
      Mono (coefficientHeartOpenCounit Λ F (V k))) ∧
    coefficientHeartFiltrationStep Λ F (V 0) = ⊥ ∧
    coefficientHeartFiltrationStep Λ F (V (Fin.last R.n)) = ⊤ ∧
    ∃ h : ∀ a : Fin R.n,
      coefficientHeartFiltrationStep Λ F (V a.castSucc) ≤
        coefficientHeartFiltrationStep Λ F (V a.succ),
      ∀ a : Fin R.n,
        Nonempty (cokernel (Subobject.ofLE
          (coefficientHeartFiltrationStep Λ F (V a.castSucc))
          (coefficientHeartFiltrationStep Λ F (V a.succ)) (h a)) ≅
          (coefficientHeartLocallyClosedExtension Λ
            (R.immersion a) (R.isImmersion a)).obj
              ((CondensedRing.upperStar Λ (R.immersion a)).obj F)) := by
  classical
  let ε (W : X.Opens) := coefficientHeartOpenCounit Λ F W
  have hm (W : X.Opens) : Mono (ε W) :=
    CondensedRing.mono_condensed_counit Λ W.ι F
  have h0 : V 0 = ⊥ := by
    ext x
    simp [hV]
  have htop : V (Fin.last R.n) = ⊤ := by
    apply SetLike.coe_injective
    rw [hV]
    simpa using R.iUnion_stratum_eq_univ
  have hnest (a : Fin R.n) : V a.castSucc ≤ V a.succ := by
    intro x hx
    rw [← SetLike.mem_coe, hV] at hx ⊢
    obtain ⟨b, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hb, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨by simpa using Nat.lt_succ_of_lt hb, hx⟩⟩
  have hbot : coefficientHeartFiltrationStep Λ F (V 0) = ⊥ := by
    have : Mono (coefficientHeartOpenCounit Λ F (V 0)) := hm _
    rw [coefficientHeartFiltrationStep, imageSubobject_mono]
    apply Subobject.mk_eq_bot_iff_zero.mpr
    have hz : IsZero ((CondensedRing.upperStar Λ (V 0).ι).obj F) := by
      have : IsEmpty (V 0).toScheme := ⟨fun x ↦ by
        have hx : x.val ∈ (V 0 : Set X) := x.2
        have hempty : (V 0 : Set X) = ∅ := congrArg SetLike.coe h0
        exact Set.notMem_empty x.val (hempty ▸ hx)⟩
      exact CondensedRing.module_zero_of_empty _ _
    have hz' : IsZero (coefficientHeartOpenTerm Λ F (V 0)) :=
      (CondensedRing.openImmersionLowerShriek Λ (V 0).ι).map_isZero hz
    exact hz'.eq_of_src (coefficientHeartOpenCounit Λ F (V 0)) 0
  have hlast : coefficientHeartFiltrationStep Λ F (V (Fin.last R.n)) = ⊤ := by
    have : Mono (coefficientHeartOpenCounit Λ F (V (Fin.last R.n))) := hm _
    rw [coefficientHeartFiltrationStep, imageSubobject_mono]
    have hi : IsIso (coefficientHeartOpenCounit Λ F (V (Fin.last R.n))) := by
      have : IsIso (V (Fin.last R.n)).ι := by
        apply (isIso_iff_isOpenImmersion_and_surjective _).2
        refine ⟨inferInstance, ⟨?_⟩⟩
        intro x
        have hx : x ∈ (V (Fin.last R.n) : Set X) := by
          simp only [htop, TopologicalSpace.Opens.coe_top, Set.mem_univ]
        exact ⟨⟨x, hx⟩, rfl⟩
      exact CondensedRing.iso_condensed_counit Λ _ F
    exact Subobject.mk_eq_top_of_isIso _
  have hs (a : Fin R.n) :
      ∃ h : coefficientHeartFiltrationStep Λ F (V a.castSucc) ≤
          coefficientHeartFiltrationStep Λ F (V a.succ),
        Nonempty (cokernel (Subobject.ofLE _ _ h) ≅
          (coefficientHeartLocallyClosedExtension Λ
            (R.immersion a) (R.isImmersion a)).obj
            ((CondensedRing.upperStar Λ (R.immersion a)).obj F)) := by
    let W := V a.castSucc
    let T := V a.succ
    have haT : R.stratum a ⊆ (T : Set X) := by
      intro x hx
      rw [show (T : Set X) = _ from hV a.succ]
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨Nat.lt_succ_self _, hx⟩⟩
    have hdiff (x : T.toScheme) : T.ι x ∉ W ↔ T.ι x ∈ R.stratum a := by
      constructor
      · intro hx
        have hxT : T.ι x ∈ (T : Set X) := x.property
        rw [show (T : Set X) = _ from hV a.succ] at hxT
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxT
        obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
        by_cases hba : b = a
        · simpa [hba] using hxb
        · apply False.elim (hx ?_)
          rw [← SetLike.mem_coe, show (W : Set X) = _ from hV a.castSucc]
          refine Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨?_, hxb⟩⟩
          have hne : b.val ≠ a.val := fun h ↦ hba (Fin.ext h)
          change b.val < a.val
          change b.val < a.val + 1 at hb
          omega
      · intro hx hxW
        rw [← SetLike.mem_coe, show (W : Set X) = _ from hV a.castSucc] at hxW
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxW
        obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
        have hba : b ≠ a := by
          intro he
          subst b
          exact (Nat.lt_irrefl a.val) hb
        exact Set.disjoint_left.mp (R.pairwise_disjoint_stratum hba) hxb hx
    have : IsImmersion (R.immersion a) := R.isImmersion a
    let t := IsOpenImmersion.lift T.ι (R.immersion a) (by
      rw [T.range_ι, R.range_immersion]
      exact haT)
    have htv : t ≫ T.ι = R.immersion a := IsOpenImmersion.lift_fac _ _ _
    have : IsImmersion (t ≫ T.ι) := htv.symm ▸ inferInstance
    have : IsImmersion t := IsImmersion.of_comp t T.ι
    have ht : Set.range t = {x | T.ι x ∉ W} := by
      ext x
      rw [Set.mem_ofPred_eq, hdiff]
      constructor
      · rintro ⟨y, rfl⟩
        rw [← R.range_immersion a]
        exact ⟨y, (congrArg (fun f ↦ f y) htv).symm⟩
      · intro hx
        rw [← R.range_immersion a] at hx
        obtain ⟨y, hy⟩ := hx
        refine ⟨y, T.ι.isEmbedding.injective ?_⟩
        exact (congrArg (fun f ↦ f y) htv).trans hy
    have : IsClosedImmersion t := IsClosedImmersion.of_isPreimmersion t (by
      rw [ht]
      exact (W.isOpen.preimage T.ι.continuous).isClosed_compl)
    exact nestedOpen_quotient Λ W T (hnest a) (R.immersion a) t htv ht F
  exact ⟨fun k ↦ hm (V k), hbot, hlast, Classical.axiomOfChoice hs⟩

set_option linter.unusedVariables false in
/-- The given ordered adapted stratification produces the counit filtration, with its
successive quotients the extensions by zero of the lisse restrictions. `V` is simply a
presentation of the open prefixes; its carrier equation fixes every V_k, including
V_0 and V_m. No connectedness or strictness condition is imposed.

Source: blueprint lemma-constructible-sheaves--7 and its proof
(blueprint: lemma-constructible-sheaves--7).

Proof:
1. The actual open counits are monic. The empty prefix has zero restriction and zero
extension; the full prefix inclusion is an isomorphism. Their images are therefore
bottom and top.
2. Consecutive open prefixes differ by exactly the given stratum. Lift its immersion
into the larger prefix and use its closed image to obtain a closed immersion there.
The open-filtration successor theorem gives a map between the two open extensions,
its counit identity over F, and its cokernel. Monicity identifies the counit images
with their represented subobjects. The existing subobject cokernel comparison and
preservation of cokernels by evaluation give the required quotient object.
3. The closed-then-open extension vanishes after restriction along every map whose
image misses the stratum. Its restriction to the stratum is the original module,
by the open unit and closed counit. Closed support reconstructs it from the closure;
open support inside the closure reconstructs it from the stratum. Composing these
adjunction isomorphisms gives the specified open-then-closed extension.
4. The existing common-stratification lisse theorem, applied to the stratification
and its identity refinement, makes every adapted restriction lisse. -/
theorem coefficientHeart_filtration (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) X))
    (hF : IsConstantModelConstructible (coefficientHeartRingObj L) X F)
    (R : X.FiniteLocallyClosedStratification)
    (hadapt : ∀ a : Fin R.n,
      HasFiniteConstantLocalModel (coefficientHeartRingObj L) (R.domain a)
        ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F))
    (V : Fin (R.n + 1) → X.Opens)
    (hV : ∀ k : Fin (R.n + 1),
      (V k : Set X) = ⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) :
    (∀ k : Fin (R.n + 1),
      Mono (coefficientHeartOpenCounit (coefficientHeartRingObj L) F (V k))) ∧
    coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V 0) = ⊥ ∧
    coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V (Fin.last R.n)) = ⊤ ∧
    ∃ h : ∀ a : Fin R.n,
      coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.castSucc) ≤
        coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.succ),
      ∀ a : Fin R.n,
        Nonempty (cokernel (Subobject.ofLE
          (coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.castSucc))
          (coefficientHeartFiltrationStep (coefficientHeartRingObj L) F (V a.succ)) (h a)) ≅
          (coefficientHeartLocallyClosedExtension (coefficientHeartRingObj L)
            (R.immersion a) (R.isImmersion a)).obj
              ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F)) ∧
        IsLisseCoefficientModule (coefficientHeartRingObj L)
          ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F) := by
  obtain ⟨hm, hbot, htop, h, eh⟩ := openPrefix_filtration (coefficientHeartRingObj L) X F R V hV
  refine ⟨hm, hbot, htop, h, fun a ↦ ⟨eh a, ?_⟩⟩
  exact (coefficientHeart_commonStratification_lisse ℓ L X hL).2 R R F hadapt
    (fun a ↦ ⟨a, Set.Subset.rfl⟩) a

end AlgebraicGeometry.ProEtale
