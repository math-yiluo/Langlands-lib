import Langlands.Analysis.HilbertSchmidtCompactStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Ring

noncomputable section

open Filter
open scoped Topology

namespace Langlands.Analysis.OperatorIdeals

universe u v w

variable {E : Type u} {F : Type v} {ι : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem opNorm_le_basis_sum (b : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] F) (h : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    ‖T‖ ≤ Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) := by
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) (fun x => ?_)
  have hx := T.hasSum (b.hasSum_repr x)
  simp only [map_smul] at hx
  refine le_of_tendsto hx.norm (Eventually.of_forall (fun s => ?_))
  have hnorm :
      ‖∑ i ∈ s, b.repr x i • T (b i)‖ ≤
        ∑ i ∈ s, ‖b.repr x i‖ * ‖T (b i)‖ := by
    simpa only [norm_smul] using
      (norm_sum_le s (fun i => b.repr x i • T (b i)))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => ‖b.repr x i‖) (fun i => ‖T (b i)‖)
  have hb : ∑ i ∈ s, ‖b.repr x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [HilbertBasis.repr_apply_apply] using
      (b.orthonormal.sum_inner_products_le x (s := s))
  have ht : ∑ i ∈ s, ‖T (b i)‖ ^ 2 ≤ ∑' i, ‖T (b i)‖ ^ 2 :=
    h.sum_le_tsum s (fun _ _ => sq_nonneg _)
  have hs0 : 0 ≤ ∑ i ∈ s, ‖T (b i)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq :
      ‖∑ i ∈ s, b.repr x i • T (b i)‖ ^ 2 ≤
        (Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) * ‖x‖) ^ 2 := by
    calc
      _ ≤ (∑ i ∈ s, ‖b.repr x i‖ * ‖T (b i)‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
          (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 hnorm
      _ ≤ (∑ i ∈ s, ‖b.repr x i‖ ^ 2) * ∑ i ∈ s, ‖T (b i)‖ ^ 2 := hcs
      _ ≤ ‖x‖ ^ 2 * ∑' i, ‖T (b i)‖ ^ 2 :=
        mul_le_mul hb ht hs0 (sq_nonneg _)
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))]
        ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 hsq

private def basisTruncation (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] F)
    (s : Finset ι) : E →L[ℂ] F :=
  ∑ i ∈ s, (innerSL ℂ (b i)).smulRight (A (b i))

omit [CompleteSpace E] [CompleteSpace F] in
private theorem basisTruncation_basis [DecidableEq ι] (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] F) (s : Finset ι) (i : ι) :
    basisTruncation b A s (b i) = if i ∈ s then A (b i) else 0 := by
  classical
  simp [basisTruncation, orthonormal_iff_ite.1 b.orthonormal]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem basisTruncation_compact (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] F) (s : Finset ι) :
    IsCompactOperator (basisTruncation b A s) := by
  change (∑ i ∈ s, (innerSL ℂ (b i)).smulRight (A (b i))) ∈
    compactOperator (RingHom.id ℂ) E F
  apply Submodule.sum_mem
  intro i _
  change IsCompactOperator ((innerSL ℂ (b i)).smulRight (A (b i)))
  have hi := isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ (b i))
  convert! hi.clm_comp (ContinuousLinearMap.toSpanSingleton ℂ (A (b i))) using 1

omit [CompleteSpace E] [CompleteSpace F] in
private theorem basisTruncation_tail_bound (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] F) (h : Summable (fun i => ‖A (b i)‖ ^ 2))
    (s : Finset ι) :
    ‖A - basisTruncation b A s‖ ≤
      Real.sqrt (∑' i : { i // i ∉ s }, ‖A (b i)‖ ^ 2) := by
  classical
  have heq : (fun i => ‖(A - basisTruncation b A s) (b i)‖ ^ 2) =
      ((s : Set ι)ᶜ).indicator (fun i => ‖A (b i)‖ ^ 2) := by
    funext i
    by_cases hi : i ∈ s <;>
      simp [basisTruncation_basis, hi]
  have hs : Summable (fun i => ‖(A - basisTruncation b A s) (b i)‖ ^ 2) := by
    rw [heq]
    exact h.indicator _
  calc
    _ ≤ Real.sqrt (∑' i, ‖(A - basisTruncation b A s) (b i)‖ ^ 2) :=
      opNorm_le_basis_sum b _ hs
    _ = _ := by
      congr 1
      rw [heq, ← tsum_subtype]
      rfl

omit [CompleteSpace E] in
private theorem compact_of_summable_basis (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] F) (h : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    IsCompactOperator A := by
  have ht : Tendsto
      (fun s : Finset ι => Real.sqrt (∑' i : { i // i ∉ s }, ‖A (b i)‖ ^ 2))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_tsum_compl_atTop_zero (fun i => ‖A (b i)‖ ^ 2))
  have hn : Tendsto (fun s : Finset ι => ‖A - basisTruncation b A s‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun s => basisTruncation_tail_bound b A h s) ht
  have hc : Tendsto (fun s : Finset ι => basisTruncation b A s) atTop (𝓝 A) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hn
  exact isCompactOperator_of_tendsto hc
    (Eventually.of_forall (basisTruncation_compact b A))

theorem hilbertSchmidtCompact : HilbertSchmidtCompactStatement.{u, v} := by
  intro E F _ _ _ _ _ _ A h
  obtain ⟨s, b, hb⟩ := h
  exact compact_of_summable_basis b A hb

end Langlands.Analysis.OperatorIdeals
