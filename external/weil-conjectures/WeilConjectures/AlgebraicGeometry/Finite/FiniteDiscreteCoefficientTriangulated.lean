/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
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
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
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
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
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
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleKernels

/-!

# Bounded constructible module objects over `T̲` and `O̲` form triangulated subcategories

This file is the counterpart, for the two coefficient rings of the module
`FiniteDiscreteCoefficient`
in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitBallRingObj`,
of the instances
`ProEtale.isTriangulated_boundedConstructible_padicIntegersRingObj`,
`ProEtale.isTriangulated_boundedConstructible_continuousMapRingObj` and
`ProEtale.isTriangulated_boundedConstructible_padicAlgClRingObj` of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`: on a topologically noetherian
scheme `X`, the bounded constructible complexes of module objects over

* `T̲ = Profinite.continuousMapRingObj T`, `T` a finite discrete ring
  (`ProEtale.isTriangulated_boundedConstructible_finiteDiscreteRingObj`), and over
* `O̲ = Profinite.continuousMapRingObj O`, `O` the closed unit ball of a finite normed extension
  `E` of `ℚ_ℓ` (`ProEtale.isTriangulated_boundedConstructible_unitBallRingObj`),

form a triangulated subcategory of the derived category. As there, this follows from the
constructible module objects being closed under kernels, cokernels and extensions: for `T` by the
finite discrete kernel theorem `finiteDiscrete_constructible_kernel`, for `O` by the integral Serre
theorem `integralConstructible_serre` for the valuation ring `continuousIntegers ℓ E`, which is the
closed unit ball.

-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CondensedRing

variable (X : Scheme.{u})

/-- For a finite discrete ring `T`, the bounded constructible complexes of `T_X`-modules on a
topologically noetherian scheme form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible_finiteDiscreteRingObj
    [TopologicalSpace.NoetherianSpace X] (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [DiscreteTopology T] [Finite T] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X)).IsTriangulated := by
  obtain ⟨hc, he⟩ := constructible_cokernels_extensions X
    (condensedRingObj (Profinite.continuousMapRingObj T) X)
  exact isTriangulated_boundedConstructible_of_serre _
    (fun M N f hM hN ↦ ⟨finiteDiscrete_constructible_kernel T X M N f hM hN,
      ObjectProperty.prop_cokernel _ f hM hN⟩)
    (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)

-- The prime `ℓ` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
/-- For the closed unit ball `O` of a finite normed extension `E` of `ℚ_ℓ`, the bounded
constructible complexes of `O_X`-modules on a topologically noetherian scheme form a triangulated
subcategory. -/
instance isTriangulated_boundedConstructible_unitBallRingObj
    [TopologicalSpace.NoetherianSpace X] (ℓ : ℕ) [Fact ℓ.Prime] {E : Type} [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (O : Subring E)
    [hO : Fact (∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1)] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} O) X)).IsTriangulated := by
  obtain rfl : O = continuousIntegers ℓ E := by
    ext x
    rw [hO.out]
    change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
  obtain ⟨hker, hcok, hext⟩ := integralConstructible_serre ℓ E X
  exact isTriangulated_boundedConstructible_of_serre _
    (fun M N f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
      ObjectProperty.prop_cokernel _ f hM hN⟩)
    (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)

set_option linter.unusedVariables false in
/-- For a noetherian scheme, bounded constructible complexes are triangulated for each
allowed coefficient ring: a finite extension field, its ring of integers, the algebraic closure,
or a finite discrete ring killed by a power of the fixed prime. The ring objects carry their
canonical commutative ring-object structures.

Proof: each of the four clauses is one of the instances above, found by typeclass inference.
Each instance is the weak-Serre argument of the blueprint proof:
the constructible modules (`IsConstructibleModuleObject`) contain `0`, are stable under
isomorphisms, and are closed under kernels, cokernels and extensions, so by Stacks 06UQ
(lem-sbc-cohomology-in-weak-serre-subcategory) the bounded complexes with constructible
cohomology form a triangulated subcategory.
1. `E̲`, `𝒪̲_E`, `ℚ̲̄_ℓ`: the instances `isTriangulated_boundedConstructible_continuousMapRingObj`,
   `_padicIntegersRingObj`, `_padicAlgClRingObj`
   (lem-sfb-bounded-constructible-triangulated-finiteness), with the closures from
   lem-weil-pbc-condensed-constructible-serre and lem-weil-pbc-integral-constructible-serre.
2. `T̲`: the instance `isTriangulated_boundedConstructible_finiteDiscreteRingObj`, with kernels by
   lem-sfb-finite-discrete-internal-constructible-kernels and cokernels and extensions by
   lem-weil-pbc-constructible-cokernels-extensions; the hypothesis `ℓ ^ n T = 0` is not needed.
(blueprint: prop-sfb-bounded-constructible-triangulated) -/
theorem isTriangulated_boundedConstructible
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
      [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
      [Algebra E (PadicAlgCl ℓ)] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)],
      (boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).IsTriangulated) ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E]
      [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E],
      (boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).IsTriangulated) ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).IsTriangulated) ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime] (T : Type) [CommRing T] [TopologicalSpace T]
      [IsTopologicalRing T] [DiscreteTopology T] [Finite T]
      (hT : ∃ n : ℕ, ∀ t : T, (ℓ : T) ^ n * t = 0),
      (boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X)).IsTriangulated) := by
  constructor
  · intro ℓ instℓ E _ _ _ _ _
    infer_instance
  constructor
  · intro ℓ instℓ E _ _ _ _ _
    infer_instance
  constructor
  · intro ℓ instℓ
    infer_instance
  · intro ℓ instℓ T _ _ _ _ _ _
    infer_instance


end AlgebraicGeometry.ProEtale
