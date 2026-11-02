import Langlands.Analysis.TraceNormBasisStatement
import Langlands.Analysis.HilbertSchmidtBasisProof

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v w

variable {E : Type u} {ι : Type v} {κ : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem traceNorm_diagonal_eq_norm_sq (A : E →L[ℂ] E) (x : E) :
    (inner ℂ x (leftModulus A x)).re = ‖CFC.sqrt (leftModulus A) x‖ ^ 2 := by
  let B := CFC.sqrt (leftModulus A)
  have hBsq : B * B = leftModulus A :=
    CFC.sqrt_mul_sqrt_self (leftModulus A) (CFC.sqrt_nonneg (A * star A))
  have hBadj : B.adjoint = B :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp
      (ContinuousLinearMap.nonneg_iff_isPositive.mp
        (CFC.sqrt_nonneg (leftModulus A))).isSelfAdjoint
  symm
  change ‖B x‖ ^ 2 = _
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, hBadj]
  change (inner ℂ x ((B * B) x)).re = _
  rw [hBsq]

private theorem traceNorm_basis_pair (A : E →L[ℂ] E)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    (Summable (fun i => (inner ℂ (b i) (leftModulus A (b i))).re) ↔
      Summable (fun j => (inner ℂ (c j) (leftModulus A (c j))).re)) ∧
    (Summable (fun i => (inner ℂ (b i) (leftModulus A (b i))).re) →
      traceNormIn b A = traceNormIn c A) := by
  simpa only [traceNormIn, traceNorm_diagonal_eq_norm_sq] using
    hilbertSchmidtBasisIndependence E E ι κ (CFC.sqrt (leftModulus A)) b c

private theorem traceClass_iff_diagonal_summable (A : E →L[ℂ] E)
    (b : HilbertBasis ι ℂ E) :
    IsTraceClass A ↔
      Summable (fun i => (inner ℂ (b i) (leftModulus A (b i))).re) := by
  constructor
  · rintro ⟨s, d, hd⟩
    exact (traceNorm_basis_pair A d b).1.mp hd
  · intro hb
    obtain ⟨s, d, _⟩ := exists_hilbertBasis ℂ E
    exact ⟨s, d, (traceNorm_basis_pair A b d).1.mp hb⟩

theorem traceNormBasisIndependence :
    TraceNormBasisIndependenceStatement.{u, v, w} := by
  intro E _ _ _ A ι κ b c
  exact ⟨traceClass_iff_diagonal_summable A b, traceNorm_basis_pair A b c⟩

end Langlands.Analysis.OperatorIdeals
