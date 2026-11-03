import Langlands.Analysis.OperatorIdeals

namespace Langlands.Analysis.OperatorIdeals

universe u v w z

/-- Rectangular Hilbert–Schmidt products have absolutely summable complex
diagonals, and their specified-basis sums satisfy the cyclic identity. -/
def HilbertSchmidtProductTraceStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ι : Type w) (κ : Type z)
    (B : E →L[ℂ] F) (C : F →L[ℂ] E)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F),
    IsHilbertSchmidt B → IsHilbertSchmidt C →
      Summable (fun i => ‖inner ℂ (b i) ((C.comp B) (b i))‖) ∧
      Summable (fun j => ‖inner ℂ (d j) ((B.comp C) (d j))‖) ∧
      traceIn b (C.comp B) = traceIn d (B.comp C)

end Langlands.Analysis.OperatorIdeals
