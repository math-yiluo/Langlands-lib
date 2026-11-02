import Langlands.Analysis.OperatorIdeals

/-!
# Trace-class operators are Hilbert–Schmidt

The trace-class predicate uses the positive left modulus `sqrt(A A*)`.
No separability assumption is imposed on the complex Hilbert space.
-/

namespace Langlands.Analysis.OperatorIdeals

universe u

/-- Summability of the positive left-modulus diagonal implies square
summability of the operator on a Hilbert basis. -/
def TraceClassHilbertSchmidtStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E),
    IsTraceClass A → IsHilbertSchmidt A

end Langlands.Analysis.OperatorIdeals
