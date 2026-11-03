import Langlands.Analysis.OperatorIdeals
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace Langlands.Analysis.OperatorIdeals

universe u v

/-- Trace-class endomorphisms form a complex vector space, are invariant under
adjoints, and remain trace class after a bounded rectangular sandwich. -/
def TraceClassIdealStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F],
    IsTraceClass (0 : E →L[ℂ] E) ∧
    (∀ (A D : E →L[ℂ] E),
      IsTraceClass A → IsTraceClass D → IsTraceClass (A + D)) ∧
    (∀ (c : ℂ) (A : E →L[ℂ] E),
      IsTraceClass A → IsTraceClass (c • A)) ∧
    (∀ (A : E →L[ℂ] E), IsTraceClass A ↔ IsTraceClass A.adjoint) ∧
    (∀ (A : E →L[ℂ] E) (B : E →L[ℂ] F) (C : F →L[ℂ] E),
      IsTraceClass A → IsTraceClass ((B.comp A).comp C))

end Langlands.Analysis.OperatorIdeals
