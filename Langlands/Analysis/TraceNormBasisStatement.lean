import Langlands.Analysis.OperatorIdeals

/-!
# Trace-class basis characterization and trace-norm basis independence

The diagonal of the positive left modulus is summable in every Hilbert
basis exactly when the operator is trace class. Its sum is then independent
of the chosen basis.
-/

namespace Langlands.Analysis.OperatorIdeals

universe u v w

/-- The witnessing-basis trace-class predicate is equivalent to summability
in any specified Hilbert basis; changing bases preserves summability and,
when summable, the trace-norm sum. -/
def TraceNormBasisIndependenceStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E)
    (ι : Type v) (κ : Type w)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E),
    (IsTraceClass A ↔
      Summable (fun i => (inner ℂ (b i) (leftModulus A (b i))).re)) ∧
    (Summable (fun i => (inner ℂ (b i) (leftModulus A (b i))).re) ↔
      Summable (fun j => (inner ℂ (c j) (leftModulus A (c j))).re)) ∧
    (Summable (fun i => (inner ℂ (b i) (leftModulus A (b i))).re) →
      traceNormIn b A = traceNormIn c A)

end Langlands.Analysis.OperatorIdeals
