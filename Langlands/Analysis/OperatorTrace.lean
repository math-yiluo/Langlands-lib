import Langlands.Analysis.OperatorIdeals

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The complex diagonal sum in one chosen Hilbert basis. Its basis-independent
trace interpretation and linear laws apply on the trace-class domain. -/
def operatorTrace (A : E →L[ℂ] E) : ℂ :=
  traceIn (Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))) A

end Langlands.Analysis.OperatorIdeals
