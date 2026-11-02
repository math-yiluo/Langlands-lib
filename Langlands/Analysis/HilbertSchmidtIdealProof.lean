import Langlands.Analysis.HilbertSchmidtIdealStatement
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section

open scoped ENNReal

namespace Langlands.Analysis.OperatorIdeals

universe u v w z t

variable {E : Type u} {F : Type v} {G : Type w} {ι : Type z} {κ : Type t}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace E] in
private theorem ideal_basis_hasSum_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using
    (lp.hasSum_norm (p := 2) (by norm_num) (b.repr x))

omit [CompleteSpace E] in
private theorem ideal_basis_ennreal_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    (∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖ ^ 2)) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (ideal_basis_hasSum_norm_sq b x).summable,
    (ideal_basis_hasSum_norm_sq b x).tsum_eq]

private theorem ideal_basis_ennreal_adjoint (A : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) :
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
      ∑' j, ENNReal.ofReal (‖A.adjoint (d j)‖ ^ 2) := by
  calc
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
        ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (d j) (A (b i))‖ ^ 2) := by
          apply tsum_congr
          intro i
          exact (ideal_basis_ennreal_norm_sq d (A (b i))).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (d j) (A (b i))‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = ∑' j, ∑' i,
        ENNReal.ofReal (‖inner ℂ (b i) (A.adjoint (d j))‖ ^ 2) := by
          apply tsum_congr
          intro j
          apply tsum_congr
          intro i
          rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑' j, ENNReal.ofReal (‖A.adjoint (d j)‖ ^ 2) := by
      apply tsum_congr
      intro j
      exact ideal_basis_ennreal_norm_sq b (A.adjoint (d j))

private theorem ideal_adjoint_summable (A : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F)
    (h : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    Summable (fun j => ‖A.adjoint (d j)‖ ^ 2) := by
  have hd : (∑' j, ENNReal.ofReal (‖A.adjoint (d j)‖ ^ 2)) ≠ ∞ := by
    rw [← ideal_basis_ennreal_adjoint A b d]
    exact h.tsum_ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hd

theorem isHilbertSchmidt_adjoint (A : E →L[ℂ] F) (h : IsHilbertSchmidt A) :
    IsHilbertSchmidt A.adjoint := by
  obtain ⟨s, b, hb⟩ := h
  obtain ⟨t, d, _⟩ := exists_hilbertBasis ℂ F
  exact ⟨t, d, ideal_adjoint_summable A b d hb⟩

theorem isHilbertSchmidt_adjoint_iff (A : E →L[ℂ] F) :
    IsHilbertSchmidt A ↔ IsHilbertSchmidt A.adjoint := by
  refine ⟨isHilbertSchmidt_adjoint A, fun h => ?_⟩
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    isHilbertSchmidt_adjoint A.adjoint h

private theorem ideal_summable_basis (A : E →L[ℂ] F) (h : IsHilbertSchmidt A)
    (b : HilbertBasis ι ℂ E) : Summable (fun i => ‖A (b i)‖ ^ 2) := by
  obtain ⟨s, c, hc⟩ := h
  obtain ⟨t, d, _⟩ := exists_hilbertBasis ℂ F
  have hd := ideal_adjoint_summable A c d hc
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    ideal_adjoint_summable A.adjoint d b hd

omit [CompleteSpace F] in
theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : E →L[ℂ] F) := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ E
  refine ⟨s, b, ?_⟩
  simpa only [zero_apply, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
    (summable_zero : Summable (fun _ : s => (0 : ℝ)))

theorem isHilbertSchmidt_add (A B : E →L[ℂ] F)
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsHilbertSchmidt (A + B) := by
  obtain ⟨s, b, hb⟩ := hA
  have hc := ideal_summable_basis B hB b
  refine ⟨s, b, ?_⟩
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => ?_) ((hb.add hc).mul_left 2)
  change ‖A (b i) + B (b i)‖ ^ 2 ≤ 2 * (‖A (b i)‖ ^ 2 + ‖B (b i)‖ ^ 2)
  have h := norm_add_le (A (b i)) (B (b i))
  have h0 := norm_nonneg (A (b i) + B (b i))
  nlinarith [sq_nonneg (‖A (b i)‖ - ‖B (b i)‖)]

omit [CompleteSpace E] [CompleteSpace F] in
theorem isHilbertSchmidt_smul (c : ℂ) (A : E →L[ℂ] F)
    (hA : IsHilbertSchmidt A) : IsHilbertSchmidt (c • A) := by
  obtain ⟨s, b, hb⟩ := hA
  refine ⟨s, b, ?_⟩
  simpa only [smul_apply, norm_smul, mul_pow] using
    hb.mul_left (‖c‖ ^ 2)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
theorem isHilbertSchmidt_postcomp (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hA : IsHilbertSchmidt A) : IsHilbertSchmidt (B.comp A) := by
  obtain ⟨s, b, hb⟩ := hA
  refine ⟨s, b, ?_⟩
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => ?_) (hb.mul_left (‖B‖ ^ 2))
  change ‖B (A (b i))‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖A (b i)‖ ^ 2
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    (B.le_opNorm (A (b i)))

theorem isHilbertSchmidt_precomp (A : E →L[ℂ] F) (C : G →L[ℂ] E)
    (hA : IsHilbertSchmidt A) : IsHilbertSchmidt (A.comp C) := by
  apply (isHilbertSchmidt_adjoint_iff (A.comp C)).2
  rw [ContinuousLinearMap.adjoint_comp]
  exact isHilbertSchmidt_postcomp A.adjoint C.adjoint (isHilbertSchmidt_adjoint A hA)

theorem hilbertSchmidtIdeal : HilbertSchmidtIdealStatement.{u, v, w} := by
  intro E F G _ _ _ _ _ _ _ _ _
  exact ⟨isHilbertSchmidt_zero, isHilbertSchmidt_add,
    isHilbertSchmidt_smul, isHilbertSchmidt_adjoint_iff,
    isHilbertSchmidt_postcomp, isHilbertSchmidt_precomp⟩

end Langlands.Analysis.OperatorIdeals
