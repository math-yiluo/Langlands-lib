import Langlands.Global.Factors.HeckeProductFormula
import Langlands.Global.Hecke.MixedSpaceFourier

/-! # Actual additive product formula in the mixed embedding -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField NumberField.InfinitePlace
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open scoped Real FourierTransform

variable {K : Type u} [Field K] [NumberField K]

/-- The supplied real local scales, indexed by the real places of the mixed space. -/
def mixedRealScale (aR : ∀ v : InfinitePlace K, v.IsReal → ℝˣ) :
    {v : InfinitePlace K // v.IsReal} → ℝ :=
  fun v => aR v.1 v.2

/-- The supplied complex trace scales, indexed by the complex places of the mixed space. -/
def mixedComplexScale (aC : ∀ v : InfinitePlace K, v.IsComplex → ℂˣ) :
    {v : InfinitePlace K // v.IsComplex} → ℂ :=
  fun v => aC v.1 v.2

omit [NumberField K] in
theorem mixedRealScale_ne_zero (aR : ∀ v : InfinitePlace K, v.IsReal → ℝˣ)
    (v : {v : InfinitePlace K // v.IsReal}) : mixedRealScale aR v ≠ 0 :=
  (aR v.1 v.2).ne_zero

omit [NumberField K] in
theorem mixedComplexScale_ne_zero (aC : ∀ v : InfinitePlace K, v.IsComplex → ℂˣ)
    (v : {v : InfinitePlace K // v.IsComplex}) : mixedComplexScale aC v ≠ 0 :=
  (aC v.1 v.2).ne_zero

set_option backward.isDefEq.respectTransparency false in
/-- The entire archimedean product is the positive mixed-space Fourier character. -/
theorem infinite_additive_product_eq_mixed
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (aR : ∀ v : InfinitePlace K, v.IsReal → ℝˣ)
    (aC : ∀ v : InfinitePlace K, v.IsComplex → ℂˣ)
    (hR : ∀ v hv, IsRealAdditiveComponent ψ v hv (aR v hv))
    (hC : ∀ v hv, IsComplexAdditiveComponent ψ v hv (aC v hv))
    (x : K) :
    (∏ v : InfinitePlace K,
      infiniteAdditiveRestriction ψ v (algebraMap K (InfiniteCompletion K v) x)) =
      𝐞 (Hecke.addTrace (mixedRealScale aR) (mixedComplexScale aC) (mixedEmbedding K x)) := by
  classical
  rw [prod_eq_prod_mul_prod, Hecke.addTrace_apply, AddChar.map_add_eq_mul,
    addChar_sum, addChar_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change ψ ((Pi.single v.1
      (algebraMap K (InfiniteCompletion K v.1) x) : InfiniteAdeles K), (0 : FiniteAdeles K)) = _
    rw [hR v.1 v.2, realScaledCharacter_apply]
    congr 1
    simp [mixedRealScale, Completion.ringEquivRealOfIsReal_apply,
      Completion.algebraMap_apply, Completion.extensionEmbeddingOfIsReal_coe]
  · apply Finset.prod_congr rfl
    intro v _
    change ψ ((Pi.single v.1
      (algebraMap K (InfiniteCompletion K v.1) x) : InfiniteAdeles K), (0 : FiniteAdeles K)) = _
    rw [hC v.1 v.2, complexScaledCharacter_apply, Algebra.trace_complex_apply]
    congr 1
    simp [mixedComplexScale, Completion.ringEquivComplexOfIsComplex_apply,
      Completion.algebraMap_apply, Completion.extensionEmbedding_coe]

/-- Outside the integral control, the actual restriction kills every local integer. -/
theorem finiteAdditiveRestriction_eq_one_of_integral
    (ψ : UnitaryAdditiveCharacter (Adeles K)) (v : FinitePlace K)
    (hv : v ∉ additiveIntegralControl ψ) (x : v.adicCompletionIntegers K) :
    finiteAdditiveRestriction ψ v x = 1 := by
  classical
  have h := additiveIntegralControl_spec ψ (Pi.single v x) (by
    intro w hw
    have hne : w ≠ v := fun h => hv (h ▸ hw)
    simp only [Pi.single_eq_of_ne hne])
  rw [integralAdditiveInclusion_single] at h
  exact h

/-- Diagonal triviality supplies the exact product formula with the supplied local
characters and scales, including triviality of all factors beyond the finite set. -/
theorem mixed_additive_product_formula
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (aR : ∀ v : InfinitePlace K, v.IsReal → ℝˣ)
    (aC : ∀ v : InfinitePlace K, v.IsComplex → ℂˣ)
    (hR : ∀ v hv, IsRealAdditiveComponent ψ v hv (aR v hv))
    (hC : ∀ v hv, IsComplexAdditiveComponent ψ v hv (aC v hv)) :
    ∀ x : K, ∃ S : Finset (FinitePlace K),
      (∀ v ∉ S, ψf v (algebraMap K (FiniteCompletion K v) x) = 1) ∧
        𝐞 (Hecke.addTrace (mixedRealScale aR) (mixedComplexScale aC) (mixedEmbedding K x)) *
          ∏ v ∈ S, ψf v (algebraMap K (FiniteCompletion K v) x) = 1 := by
  classical
  intro x
  let S := additiveIntegralControl ψ ∪ nonintegralPlaces (diagonal K x).2
  refine ⟨S, ?_, ?_⟩
  · intro v hv
    have hv' : v ∉ additiveIntegralControl ψ ∧
        v ∉ nonintegralPlaces (diagonal K x).2 := by simpa [S] using hv
    rw [hf v]
    exact finiteAdditiveRestriction_eq_one_of_integral ψ v hv'.1
      ⟨_, integral_of_not_mem_nonintegralPlaces _ v hv'.2⟩
  · have h := diagonal_additive_product ψ hdiag x S
      Finset.subset_union_left Finset.subset_union_right
    rw [infinite_additive_product_eq_mixed ψ aR aC hR hC] at h
    have hf' (v : FinitePlace K) (y : FiniteCompletion K v) :
        ψf v y = finiteAdditiveRestriction ψ v y := hf v y
    simpa only [← hf'] using h

end Langlands.Global.HeckeFunctionalEquation
