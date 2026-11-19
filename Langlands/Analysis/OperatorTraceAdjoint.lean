import Langlands.Analysis.OperatorTraceProof

/-! # Adjoint covariance of the Hilbert operator trace -/

noncomputable section

open scoped InnerProduct InnerProductSpace ComplexConjugate

set_option autoImplicit false

namespace Langlands.Analysis.OperatorIdeals

/-- Taking the adjoint conjugates the trace of a trace-class complex Hilbert operator. -/
theorem operatorTrace_adjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    operatorTrace T.adjoint = conj (operatorTrace T) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  rw [(operatorTraceBasis H _ ι b (isTraceClass_adjoint T hT)).2,
    (operatorTraceBasis H T ι b hT).2, traceIn, traceIn, Complex.conj_tsum]
  exact tsum_congr fun i => by
    rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

end Langlands.Analysis.OperatorIdeals
