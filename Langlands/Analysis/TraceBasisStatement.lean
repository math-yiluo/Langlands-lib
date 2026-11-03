import Langlands.Analysis.OperatorIdeals

namespace Langlands.Analysis.OperatorIdeals

universe u v w

/-- The complex diagonal of a trace-class endomorphism is absolutely
summable in every Hilbert basis, and its sum is independent of the basis. -/
def TraceBasisIndependenceStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E)
    (ι : Type v) (κ : Type w)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E),
    IsTraceClass A →
      Summable (fun i => ‖inner ℂ (b i) (A (b i))‖) ∧
      Summable (fun j => ‖inner ℂ (c j) (A (c j))‖) ∧
      traceIn b A = traceIn c A

end Langlands.Analysis.OperatorIdeals
