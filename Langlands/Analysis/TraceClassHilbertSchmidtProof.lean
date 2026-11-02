import Langlands.Analysis.TraceClassHilbertSchmidtStatement
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.NormNum

noncomputable section

open scoped ENNReal

namespace Langlands.Analysis.OperatorIdeals

universe u v w

variable {E : Type u} {ι : Type v} {κ : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem trace_leftModulus_sq (A : E →L[ℂ] E) :
    leftModulus A * leftModulus A = A * star A := by
  exact CFC.sqrt_mul_sqrt_self (A * star A) (mul_star_self_nonneg A)

private theorem trace_positive_norm_sq_le (T : E →L[ℂ] E) (hT : 0 ≤ T) (x : E) :
    ‖T x‖ ^ 2 ≤ ‖CFC.sqrt T‖ ^ 2 * (inner ℂ x (T x)).re := by
  let B := CFC.sqrt T
  have hBsq : B * B = T := CFC.sqrt_mul_sqrt_self T hT
  have hBadj : B.adjoint = B :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp
      (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSelfAdjoint
  have hdiag : ‖B x‖ ^ 2 = (inner ℂ x (T x)).re := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hBadj]
    change (inner ℂ x ((B * B) x)).re = _
    rw [hBsq]
  calc
    ‖T x‖ ^ 2 = ‖B (B x)‖ ^ 2 := by rw [← hBsq]; rfl
    _ ≤ (‖B‖ * ‖B x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (B.le_opNorm (B x))
    _ = ‖CFC.sqrt T‖ ^ 2 * (inner ℂ x (T x)).re := by rw [mul_pow, hdiag]

private theorem trace_adjoint_norm_sq_eq (A : E →L[ℂ] E) (x : E) :
    ‖A.adjoint x‖ ^ 2 = ‖leftModulus A x‖ ^ 2 := by
  have hLadj : (leftModulus A).adjoint = leftModulus A :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp
      (ContinuousLinearMap.nonneg_iff_isPositive.mp
        (CFC.sqrt_nonneg (A * star A))).isSelfAdjoint
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hLadj]
  change (inner ℂ x ((A * star A) x)).re =
    (inner ℂ x ((leftModulus A * leftModulus A) x)).re
  rw [trace_leftModulus_sq]

omit [CompleteSpace E] in
private theorem trace_basis_hasSum_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using
    (lp.hasSum_norm (p := 2) (by norm_num) (b.repr x))

omit [CompleteSpace E] in
private theorem trace_basis_ennreal_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    (∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖ ^ 2)) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (trace_basis_hasSum_norm_sq b x).summable,
    (trace_basis_hasSum_norm_sq b x).tsum_eq]

private theorem trace_basis_ennreal_adjoint (A : E →L[ℂ] E)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ E) :
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
      ∑' j, ENNReal.ofReal (‖A.adjoint (d j)‖ ^ 2) := by
  calc
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
        ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (d j) (A (b i))‖ ^ 2) := by
          apply tsum_congr
          intro i
          exact (trace_basis_ennreal_norm_sq d (A (b i))).symm
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
      exact trace_basis_ennreal_norm_sq b (A.adjoint (d j))

theorem isHilbertSchmidt_of_isTraceClass (A : E →L[ℂ] E) (hA : IsTraceClass A) :
    IsHilbertSchmidt A := by
  obtain ⟨s, b, hb⟩ := hA
  have hadj : Summable (fun i => ‖A.adjoint (b i)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
      (hb.mul_left (‖CFC.sqrt (leftModulus A)‖ ^ 2))
    rw [trace_adjoint_norm_sq_eq]
    exact trace_positive_norm_sq_le (leftModulus A)
      (CFC.sqrt_nonneg (A * star A)) (b i)
  refine ⟨s, b, ?_⟩
  have hfin : (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) ≠ ∞ := by
    rw [trace_basis_ennreal_adjoint A b b]
    exact hadj.tsum_ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hfin

theorem traceClassHilbertSchmidt : TraceClassHilbertSchmidtStatement.{u} := by
  intro E _ _ _ A hA
  exact isHilbertSchmidt_of_isTraceClass A hA

end Langlands.Analysis.OperatorIdeals
