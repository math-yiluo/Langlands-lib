import Langlands.Analysis.TraceBasisStatement
import Langlands.Analysis.TraceClassFactorizationProof
import Langlands.Analysis.HilbertSchmidtProductTraceProof

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v w

theorem traceBasisIndependence : TraceBasisIndependenceStatement.{u, v, w} := by
  intro E _ _ _ A ι κ b c hA
  obtain ⟨B, C, hB, hC, hfac⟩ := traceClassFactorization E A hA
  have hb := hilbertSchmidtProductTrace E E ι ι C B b b hC hB
  have hc := hilbertSchmidtProductTrace E E κ ι C B c b hC hB
  rw [hfac]
  exact ⟨hb.1, hc.1, hb.2.2.trans hc.2.2.symm⟩

end Langlands.Analysis.OperatorIdeals
