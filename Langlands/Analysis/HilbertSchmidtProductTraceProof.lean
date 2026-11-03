import Langlands.Analysis.HilbertSchmidtProductTraceStatement
import Langlands.Analysis.HilbertSchmidtBasisProof
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v w z

variable {E : Type u} {F : Type v} {ι : Type w} {κ : Type z}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private theorem product_basis_hasSum_norm_sq (d : HilbertBasis κ ℂ F) (x : F) :
    HasSum (fun j => ‖inner ℂ (d j) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using
    (lp.hasSum_norm (p := 2) (by norm_num) (d.repr x))

private theorem product_hs_summable_basis (B : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (hB : IsHilbertSchmidt B) :
    Summable (fun i => ‖B (b i)‖ ^ 2) := by
  obtain ⟨s, c, hc⟩ := hB
  exact ((hilbertSchmidtBasisIndependence E F s ι B c b).1).mp hc

private theorem product_matrix_sq_summable (B : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F)
    (hB : IsHilbertSchmidt B) :
    Summable (fun p : ι × κ => ‖inner ℂ (d p.2) (B (b p.1))‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
  refine ⟨fun i => (product_basis_hasSum_norm_sq d (B (b i))).summable, ?_⟩
  simpa only [(product_basis_hasSum_norm_sq d _).tsum_eq] using
    product_hs_summable_basis B b hB

private theorem product_coeff_norm_summable
    (B : E →L[ℂ] F) (C : F →L[ℂ] E)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F)
    (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) :
    Summable (fun p : ι × κ =>
      ‖inner ℂ (b p.1) (C (d p.2)) * inner ℂ (d p.2) (B (b p.1))‖) := by
  have h1 := (product_matrix_sq_summable C d b hC).prod_symm
  change Summable (fun p : ι × κ =>
    ‖inner ℂ (b p.1) (C (d p.2))‖ ^ 2) at h1
  have h2 := product_matrix_sq_summable B b d hB
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (h1.add h2)
  simp only [norm_mul]
  nlinarith [sq_nonneg (‖inner ℂ (b p.1) (C (d p.2))‖ -
    ‖inner ℂ (d p.2) (B (b p.1))‖)]

variable [CompleteSpace E] [CompleteSpace F]

private theorem product_row_sum
    (B : E →L[ℂ] F) (C : F →L[ℂ] E)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) (i : ι) :
    (∑' j, inner ℂ (b i) (C (d j)) * inner ℂ (d j) (B (b i))) =
      inner ℂ (b i) ((C.comp B) (b i)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply] using
    d.tsum_inner_mul_inner (C.adjoint (b i)) (B (b i))

private theorem product_col_sum
    (B : E →L[ℂ] F) (C : F →L[ℂ] E)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) (j : κ) :
    (∑' i, inner ℂ (b i) (C (d j)) * inner ℂ (d j) (B (b i))) =
      inner ℂ (d j) ((B.comp C) (d j)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    mul_comm] using b.tsum_inner_mul_inner (B.adjoint (d j)) (C (d j))

theorem hilbertSchmidtProductTrace :
    HilbertSchmidtProductTraceStatement.{u, v, w, z} := by
  intro E F _ _ _ _ _ _ ι κ B C b d hB hC
  let f : ι × κ → ℂ := fun p =>
    inner ℂ (b p.1) (C (d p.2)) * inner ℂ (d p.2) (B (b p.1))
  have hn : Summable (fun p => ‖f p‖) := product_coeff_norm_summable B C b d hB hC
  have hs : Summable f := hn.of_norm
  refine ⟨?_, ?_, ?_⟩
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hn.prod
    rw [← product_row_sum B C b d i]
    exact norm_tsum_le_tsum_norm (hn.prod_factor i)
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      hn.prod_symm.prod
    rw [← product_col_sum B C b d j]
    exact norm_tsum_le_tsum_norm (hn.prod_symm.prod_factor j)
  · unfold traceIn
    simp_rw [← product_row_sum B C b d, ← product_col_sum B C b d]
    exact hs.tsum_comm.symm

end Langlands.Analysis.OperatorIdeals
