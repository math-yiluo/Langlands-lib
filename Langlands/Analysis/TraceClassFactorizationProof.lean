import Langlands.Analysis.TraceClassFactorizationStatement
import Langlands.Analysis.LeftModulusFactorizationProof
import Langlands.Analysis.HilbertSchmidtIdealProof

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem factorization_diagonal_eq_norm_sq (A : E →L[ℂ] E) (x : E) :
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

theorem traceClassFactorization : TraceClassFactorizationStatement.{u} := by
  intro E _ _ _ A hA
  let B := CFC.sqrt (leftModulus A)
  have hB : IsHilbertSchmidt B := by
    obtain ⟨s, b, hb⟩ := hA
    refine ⟨s, b, ?_⟩
    simpa only [factorization_diagonal_eq_norm_sq] using hb
  obtain ⟨U, _, hfac⟩ := leftModulusFactorization E A
  have hBsq : B * B = leftModulus A :=
    CFC.sqrt_mul_sqrt_self (leftModulus A) (CFC.sqrt_nonneg (A * star A))
  refine ⟨B, B.comp U, hB, isHilbertSchmidt_precomp B U hB, ?_⟩
  rw [hfac]
  ext x
  change leftModulus A (U x) = (B * B) (U x)
  rw [hBsq]

end Langlands.Analysis.OperatorIdeals
