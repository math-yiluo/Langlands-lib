import Langlands.Analysis.OperatorIdeals

namespace Langlands.Analysis.OperatorIdeals

universe u v

/-- A composable pair of Hilbert–Schmidt maps between complex Hilbert
spaces has a trace-class endomorphism as its composition. -/
def HilbertSchmidtProductTraceClassStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (B : E →L[ℂ] F) (C : F →L[ℂ] E),
    IsHilbertSchmidt B → IsHilbertSchmidt C → IsTraceClass (C.comp B)

end Langlands.Analysis.OperatorIdeals
