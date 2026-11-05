import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology
import Langlands.AlgebraicGeometry.PointTopology.NumberFieldSIntegerWeilIntegralTopology
import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionNaturality
import Langlands.Global.SIntegerCompletedFieldTensor
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology

/-! # Actual S-integer Weil model field points and integral compatibility -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open IsDedekindDomain
open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension IntegralTensor IntegralTopology
  NumberField.LiesOver InfiniteExtension
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLocalTensor
  Langlands.Global.NumberFieldSIntegerFieldTensor

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
  (S : Finset (FinitePlace K)) (v : HeightOneSpectrum (𝓞 K))
  (Y : Over (Spec (CommRingCat.of (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)))) [LocallyOfFiniteType Y.hom]

private theorem modelFieldFactorModuleTopology (q : FinitePlacesAbove L v) :
    IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) := by
  let : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

/-- Field points of the actual integral-model Weil scheme identify with all original upper field points. -/
def numberFieldSIntegerModelFieldPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n = Y.hom) :
    letI : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K)
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
        (v.adicCompletion K)) :=
      schemePointTopology ((S : Set (FinitePlace K)).integer K)
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
        (v.adicCompletion K)
    letI : ∀ q : FinitePlacesAbove L v, TopologicalSpace
        (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L)) :=
      fun q => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L)
    RingPoint ((S : Set (FinitePlace K)).integer K)
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
        (v.adicCompletion K) ≃ₜ
      (∀ q : FinitePlacesAbove L v,
        RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L)) := by
  let : ∀ q : FinitePlacesAbove L v,
      Module.Finite (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun q => FiniteExtension.local_finite v q.1
  let : ∀ q : FinitePlacesAbove L v,
      Module.Projective (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun _ => inferInstance
  let : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) :=
    modelFieldFactorModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
    (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) Y n j hj

/-- Every upper field component retains the original integral-model Weil counit. -/
theorem numberFieldSIntegerModelFieldPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n = Y.hom)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
      (v.adicCompletion K))
    (q : FinitePlacesAbove L v) :
    numberFieldSIntegerModelFieldPointHomeomorph K L S v Y n j hj p q =
      completedTensorWeilRestrictionFactorTestMap
          ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (v.adicCompletion K)
          (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
          (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
          (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) q ≫
        affineChartWeilRestrictionComparison ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y
          (ringTest ((S : Set (FinitePlace K)).integer K) (v.adicCompletion K)) p := by
  let : ∀ q : FinitePlacesAbove L v,
      Module.Finite (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun q => FiniteExtension.local_finite v q.1
  let : ∀ q : FinitePlacesAbove L v,
      Module.Projective (v.adicCompletion K) (q.1.adicCompletion L) :=
    fun _ => inferInstance
  let : ∀ q : FinitePlacesAbove L v,
      IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) :=
    modelFieldFactorModuleTopology K L v
  have h := projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
    (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) Y n j hj p q
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
      (v.adicCompletion K)) :=
    schemePointTopology ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
      (v.adicCompletion K)
  let : ∀ q : FinitePlacesAbove L v, TopologicalSpace
      (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L)) :=
    fun q => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L)
  have hh : numberFieldSIntegerModelFieldPointHomeomorph K L S v Y n j hj =
      projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (v.adicCompletion K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
        (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
        (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) Y n j hj := rfl
  rw [hh]
  exact h

section InfinitePlace

variable (v : NumberField.InfinitePlace K)

omit [NumberField K] in
private theorem infinitePlaceFactorIsModuleTopology (q : InfinitePlacesAbove L v) :
    IsModuleTopology v.Completion q.1.Completion := by
  let := infiniteCompletionNontriviallyNormedField v
  exact isModuleTopologyOfFiniteDimensional

/-- At any infinite number-field place, including both real and complex
cases, the original Weil points identify homeomorphically with all upper points. -/
def numberFieldSIntegerModelInfinitePointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n = Y.hom) :
    letI : TopologicalSpace
        (RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y) v.Completion) :=
      schemePointTopology ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y) v.Completion
    letI : ∀ q : InfinitePlacesAbove L v, TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y q.1.Completion) :=
      fun q => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y q.1.Completion
    RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y) v.Completion ≃ₜ
      (∀ q : InfinitePlacesAbove L v, RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y q.1.Completion) := by
  letI : ∀ q : InfinitePlacesAbove L v, IsModuleTopology v.Completion q.1.Completion :=
    infinitePlaceFactorIsModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) v.Completion (fun q : InfinitePlacesAbove L v => q.1.Completion)
    (NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S v) (NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S v) Y n j hj

/-- Every infinite upper-place component retains the original counit and
the actual completion embedding through the completed-tensor factor test. -/
theorem numberFieldSIntegerModelInfinitePointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n = Y.hom)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y) v.Completion)
    (q : InfinitePlacesAbove L v) :
    numberFieldSIntegerModelInfinitePointHomeomorph K L S Y v n j hj p q =
      completedTensorWeilRestrictionFactorTestMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) v.Completion
          (fun q : InfinitePlacesAbove L v => q.1.Completion)
          (NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S v) (NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S v) q ≫
        affineChartWeilRestrictionComparison ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (ringTest ((S : Set (FinitePlace K)).integer K) v.Completion) p := by
  let : ∀ q : InfinitePlacesAbove L v, IsModuleTopology v.Completion q.1.Completion :=
    infinitePlaceFactorIsModuleTopology K L v
  exact projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) v.Completion (fun q : InfinitePlacesAbove L v => q.1.Completion)
    (NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S v) (NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S v) Y n j hj p q

end InfinitePlace

variable [Fact (v ∉ S)]

/-- Extending integral coefficients commutes with the actual original-model Weil homeomorphisms. -/
theorem numberFieldSIntegerModelFieldPointHomeomorph_integralToField
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n = Y.hom)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
      (v.adicCompletionIntegers K)) (q : FinitePlacesAbove L v) :
    numberFieldSIntegerModelFieldPointHomeomorph K L S v Y n j hj
        (p.changeRing (Algebra.algHom ((S : Set (FinitePlace K)).integer K) (v.adicCompletionIntegers K) (v.adicCompletion K))) q =
      (numberFieldSIntegerWeilRestrictionPointHomeomorph K L S v Y n j hj p q).changeRing
        (Algebra.algHom (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L)) := by
  rw [numberFieldSIntegerModelFieldPointHomeomorph_counit,
    numberFieldSIntegerWeilRestrictionPointHomeomorph_counit]
  exact completedTensorWeilRestrictionPointMap_natural
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (v.adicCompletionIntegers K) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (NumberFieldSIntegerLocalTensor.completedTensorEquiv K S v L) (NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S v L)
    (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v) (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v)
    (Algebra.algHom ((S : Set (FinitePlace K)).integer K) (v.adicCompletionIntegers K) (v.adicCompletion K))
    (fun q => Algebra.algHom (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L))
    (fun _ _ => rfl) Y p q

/-- A field point of the original Weil model is integral exactly when all its upper components are integral. -/
theorem numberFieldSIntegerModelFieldPointHomeomorph_integral_iff
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) n = Y.hom)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y) (v.adicCompletion K)) :
    (∃ z : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
        (v.adicCompletionIntegers K),
      z.changeRing (Algebra.algHom ((S : Set (FinitePlace K)).integer K) (v.adicCompletionIntegers K) (v.adicCompletion K)) = p) ↔
    ∀ q : FinitePlacesAbove L v,
      ∃ z : RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L),
        z.changeRing (Algebra.algHom (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L)) =
          numberFieldSIntegerModelFieldPointHomeomorph K L S v Y n j hj p q := by
  classical
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
      (v.adicCompletionIntegers K)) :=
    schemePointTopology ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y) (v.adicCompletionIntegers K)
  let : ∀ q : FinitePlacesAbove L v,
      TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L)) :=
    fun q => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L)
  let : TopologicalSpace (RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y)
      (v.adicCompletion K)) :=
    schemePointTopology ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y) (v.adicCompletion K)
  let : ∀ q : FinitePlacesAbove L v,
      TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L)) :=
    fun q => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L)
  let eI := numberFieldSIntegerWeilRestrictionPointHomeomorph K L S v Y n j hj
  let eF := numberFieldSIntegerModelFieldPointHomeomorph K L S v Y n j hj
  constructor
  · rintro ⟨z, rfl⟩ q
    exact ⟨eI z q, (numberFieldSIntegerModelFieldPointHomeomorph_integralToField
      K L S v Y n j hj z q).symm⟩
  · intro h
    choose t ht using h
    refine ⟨eI.symm t, ?_⟩
    apply eF.injective
    apply funext
    intro q
    change numberFieldSIntegerModelFieldPointHomeomorph K L S v Y n j hj _ q = _
    rw [numberFieldSIntegerModelFieldPointHomeomorph_integralToField]
    have he : eI (eI.symm t) q = t q := congrFun (eI.apply_symm_apply t) q
    exact (congrArg (fun z => z.changeRing
      (Algebra.algHom (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (q.1.adicCompletionIntegers L) (q.1.adicCompletion L))) he).trans (ht q)

end Langlands.AlgebraicGeometry.PointTopology
