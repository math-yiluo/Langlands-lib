import Langlands.Analysis.OperatorIdeals

namespace Langlands.Analysis.OperatorIdeals

universe u

/-- A trace-class endomorphism factors as a composition of two
Hilbert–Schmidt endomorphisms of the same Hilbert space. -/
def TraceClassFactorizationStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E),
    IsTraceClass A →
      ∃ B C : E →L[ℂ] E,
        IsHilbertSchmidt B ∧ IsHilbertSchmidt C ∧ A = B.comp C

end Langlands.Analysis.OperatorIdeals
