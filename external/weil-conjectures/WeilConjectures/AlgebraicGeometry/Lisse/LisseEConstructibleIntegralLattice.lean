/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeReducedOpen
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
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
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
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralTransport
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.ConstructibleSheaf.FreeLifting
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import all Mathlib.Topology.MetricSpace.Ultra.Basic
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Analysis.Normed.Group.Ultra
import all Mathlib.Data.Finset.Max
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import all WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
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
import all Mathlib.Algebra.Category.Grp.AB
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
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import all WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import all WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.Topology.StratificationDense
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
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
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
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
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
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
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import all WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
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
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
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
import all WeilConjectures.AlgebraicGeometry.ContinuousLisseStratifiedLattices
import all WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import all WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import all WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all Mathlib.CategoryTheory.Sites.CoversTop.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import all WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import all WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import all Mathlib.CategoryTheory.Limits.Presheaf
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import all WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Sites.Precoverage.Generates
import all Mathlib.CategoryTheory.Sites.Finite
import all Mathlib.CategoryTheory.Sites.LocalProperties
import all Mathlib.CategoryTheory.Limits.Connected
import all Mathlib.CategoryTheory.Filtered.Connected
import all Mathlib.CategoryTheory.Filtered.Final
import all Mathlib.Basic.Finite.Prod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import all WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import all WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import all WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import all WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import all WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import all WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import all Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import all WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import all WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import all WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import all WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import all Mathlib.CategoryTheory.Sites.CoverPreserving
import all Mathlib.CategoryTheory.Sites.CoversTop.Over
import all Mathlib.CategoryTheory.Sites.SheafHom
import all WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import all WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.LargeSetSheafification
import all WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import all WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import all WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import all WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all Mathlib.LinearAlgebra.TensorProduct.Pi
import all Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import all Mathlib.LinearAlgebra.TensorProduct.Basis
import all WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import all Mathlib.Topology.Algebra.OpenSubgroup
import all Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all Mathlib.Analysis.Normed.Field.WithAbs
import all Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import all Mathlib.GroupTheory.Coset.Defs
import all Mathlib.Topology.Algebra.Module.Equiv.Basic
import all Mathlib.Topology.Algebra.Module.Equiv.Pi
import all Mathlib.Topology.CompactOpen
import all Mathlib.LinearAlgebra.Basis.Defs
import all WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.RingTheory.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import all Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.CategoryTheory.Sites.Over
import all WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport
import all WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import all Mathlib.LinearAlgebra.TensorProduct.Map
import all Mathlib.CategoryTheory.ShrinkYoneda
import all Mathlib.CategoryTheory.Limits.Preserves.Ulift
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import all WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeFiniteCoproductSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionLocalModel
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalModel
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitModel
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitData
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralLocalizationSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.CondensedUnderivedPushforwardContinuitySupplement
import all WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeKernelModel
import all WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeDenominators
import all WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalization
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixKernelLocallyFree
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.Integral.IntegralContinuousEncodingConstructible

/-!
# A lisse finite-extension sheaf has a constructible integral lattice

## References

* Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13, Definitions 6.8.1, 6.8.3 and
  6.8.10
* Bhatt--Scholze, Lemma 6.8.2(1)
* Bhatt--Scholze, Lemma 6.8.13
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction
  CondensedRing.pullIso CondensedRing.upperStarComp
  CondensedRing.integralScalarMap
  CondensedRing.continuousFieldModuleEquivalence
  CondensedRing.continuousIntegerModuleEquivalence

private theorem internal_lisse_model
    (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj K) T))
    (hP : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj K) T) P) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff l K) T),
      IsConstructibleModuleObject (condensedRingObj (CondensedRing.integralCoeff l K) T) N ∧
      Nonempty ((Mod.extendScalars
        (coefficientMap (CondensedRing.integralScalarMap l K) T)).obj N ≅ P) := by
  obtain ⟨S, hS⟩ := CondensedRing.continuousLisse_stratified_lattices l K T P hP
  have hmodels (a : Fin S.n) :
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (CondensedRing.integralCoeff l K) T)),
        IsConstructibleModuleObject
          ((upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (CondensedRing.integralCoeff l K) T)) M ∧
        Nonempty ((Mod.extendScalars
          ((upperStar Ab.{u + 1} (S.immersion a)).map
            (coefficientMap (CondensedRing.integralScalarMap l K) T))).obj M ≅
          ((upperStar Ab.{u + 1} (S.immersion a)).mapMod _).obj P) := by
    obtain ⟨M, hM, ⟨eM⟩⟩ := hS a
    exact CondensedRing.pullbackCoefficient_model (CondensedRing.integralCoeff l K)
      (Profinite.continuousMapRingObj K) (CondensedRing.integralScalarMap l K)
      (X := T) (Y := S.domain a) (S.immersion a) P M hM.isConstructibleModuleObject eM
  exact CondensedRing.continuousConstructible_integral_gluing l K T P S hmodels

/-- A lisse rational sheaf has a constructible integral model, with no global freeness
requirement on that model. `WithAbs` equips the field with its canonical absolute-value
topology and transports its valuation ring; `ULift` changes only the coefficient size. -/
theorem exists_constructible_integral_lattice
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (_hℓ : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing T (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    [L.IsFiniteLocallyFree] :
    ∃ N : SheafOfModules.{u + 1} (latticeModuleRing T (latticeCoefficientIntegers l E)),
      IsContinuousConstructible T (latticeCoefficientIntegers l E) N ∧
      Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (integralLatticeCoefficientMap T l E) N ≅ L) := by
  classical
  obtain ⟨K, hK, hAK, hFK, ⟨e⟩⟩ := exists_small_coefficient l E
  let := hK
  let := hAK
  let := hFK
  let := spectralNorm.normedField ℚ_[l] K
  let := spectralNorm.normedAlgebra ℚ_[l] K
  let FE := CondensedRing.continuousFieldModuleEquivalence l K T
  let FI := CondensedRing.continuousIntegerModuleEquivalence l K T
  let er := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e T)
  let ea := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeIntegerIso l E K e T)
  let GE := CondensedRing.ringModuleEquivalenceOfIso T er
  let GI := CondensedRing.ringModuleEquivalenceOfIso T ea
  let L' := GE.inverse.obj L
  have : L'.IsFiniteLocallyFree := by
    dsimp only [L', GE, CondensedRing.ringModuleEquivalenceOfIso]
    exact finiteLocallyFree_restrict (Scheme.ProEt.topology T) _ _ er.symm L
  let P := FE.inverse.obj L'
  have hP : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.continuousMapRingObj K) T) P :=
    field_inverse_locallyFree l K T L'
  obtain ⟨N, hN, ⟨eN⟩⟩ := internal_lisse_model l K T P hP
  let M := FI.functor.obj N
  have hM : IsContinuousConstructible T (latticeCoefficientIntegers l E)
      (GI.functor.obj M) :=
    integralContinuousEncoding_constructible l E K T (nativeIntegerIso l E K e T) N hN
  obtain ⟨eS⟩ := CondensedRing.continuousModuleEncoding_scalar_extension l K T M
  let eS' := FE.functor.mapIso
    ((Mod.extendScalars (coefficientMap (CondensedRing.integralScalarMap l K) T)).mapIso
      (FI.unitIso.app N)) ≪≫ eS
  obtain ⟨es⟩ := native_scalar_iso l E K e T M
  refine ⟨GI.functor.obj M, hM, ⟨?_⟩⟩
  exact es ≪≫ GE.functor.mapIso
    (eS'.symm ≪≫ FE.functor.mapIso eN ≪≫ FE.counitIso.app L') ≪≫ GE.counitIso.app L

end AlgebraicGeometry.ProEtale
