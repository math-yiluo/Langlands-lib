import Langlands.Analysis.HilbertSchmidtEvaluationStatement
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory

namespace Langlands.Analysis.OperatorIdeals

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {X : Type v} [MeasurableSpace X] {μ : Measure X}
variable {ι : Type w}

private theorem evaluation_bessel (b : HilbertBasis ι ℂ E)
    (s : Finset ι) (l : E →L[ℂ] ℂ) :
    ∑ i ∈ s, ‖l (b i)‖ ^ 2 ≤ ‖l‖ ^ 2 := by
  let z := (InnerProductSpace.toDual ℂ E).symm l
  have hz : ‖z‖ = ‖l‖ := (InnerProductSpace.toDual ℂ E).symm.norm_map l
  have he : ∀ i, ‖l (b i)‖ = ‖inner ℂ (b i) z‖ := by
    intro i
    rw [← InnerProductSpace.toDual_symm_apply]
    exact norm_inner_symm _ _
  simpa only [he, hz] using b.orthonormal.sum_inner_products_le z (s := s)

private theorem l2_norm_sq_integral (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  change Complex.reCLM (∫ x, inner ℂ (f x) (f x) ∂μ) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner f f)]
  congr 1
  funext x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm

private theorem evaluation_basis_bound (A : E →L[ℂ] Lp ℂ 2 μ)
    (k : X → E →L[ℂ] ℂ) (g : X → ℝ) (hg : Integrable g μ)
    (hrep : ∀ z : E, (A z : X → ℂ) =ᵐ[μ] fun x => k x z)
    (hbound : ∀ᵐ x ∂μ, ‖k x‖ ^ 2 ≤ g x) (b : HilbertBasis ι ℂ E) :
    Summable (fun i => ‖A (b i)‖ ^ 2) ∧
      (∑' i, ‖A (b i)‖ ^ 2) ≤ ∫ x, g x ∂μ := by
  classical
  have hint (i : ι) : Integrable (fun x => ‖(A (b i)) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A (b i)))).mp
      (Lp.memLp (A (b i)))
  have hsum (s : Finset ι) : ∑ i ∈ s, ‖A (b i)‖ ^ 2 ≤ ∫ x, g x ∂μ := by
    calc
      ∑ i ∈ s, ‖A (b i)‖ ^ 2 = ∫ x, ∑ i ∈ s, ‖(A (b i)) x‖ ^ 2 ∂μ := by
        simp_rw [l2_norm_sq_integral]
        exact (integral_finsetSum s (fun i _ => hint i)).symm
      _ ≤ ∫ x, g x ∂μ := by
        apply integral_mono_ae (integrable_finsetSum s (fun i _ => hint i)) hg
        have hreps : ∀ᵐ x ∂μ, ∀ i ∈ s, (A (b i)) x = k x (b i) := by
          exact (eventually_all_finset s).2 (fun i _ => hrep (b i))
        filter_upwards [hreps, hbound] with x hx hb
        calc
          ∑ i ∈ s, ‖(A (b i)) x‖ ^ 2 = ∑ i ∈ s, ‖k x (b i)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hx i hi]
          _ ≤ ‖k x‖ ^ 2 := evaluation_bessel b s (k x)
          _ ≤ g x := hb
  exact ⟨summable_of_sum_le (fun i => sq_nonneg _) hsum,
    Real.tsum_le_of_sum_le (fun i => sq_nonneg _) hsum⟩

theorem hilbertSchmidtDominatedEvaluation :
    HilbertSchmidtDominatedEvaluationStatement.{u, v, w} := by
  intro E _ _ _ X _ μ A k g hg hrep hbound
  constructor
  · obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ E
    exact ⟨s, b, (evaluation_basis_bound A k g hg hrep hbound b).1⟩
  · intro ι b
    exact evaluation_basis_bound A k g hg hrep hbound b

theorem hilbertSchmidtUniformEvaluation :
    HilbertSchmidtUniformEvaluationStatement.{u, v, w} := by
  intro E _ _ _ X _ μ _ A k C _hC hrep hbound
  have hsquare : ∀ᵐ x ∂μ, ‖k x‖ ^ 2 ≤ C ^ 2 := by
    filter_upwards [hbound] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have h := hilbertSchmidtDominatedEvaluation.{u, v, w} E X μ A k (fun _ => C ^ 2)
    (integrable_const _) hrep hsquare
  simpa only [integral_const, smul_eq_mul, Measure.real,
    mul_comm (μ Set.univ).toReal] using h

theorem hilbertSchmidtEvaluationCriteria :
    HilbertSchmidtEvaluationCriteriaStatement.{u, v, w} := by
  exact ⟨hilbertSchmidtDominatedEvaluation, hilbertSchmidtUniformEvaluation⟩

end Langlands.Analysis.OperatorIdeals
