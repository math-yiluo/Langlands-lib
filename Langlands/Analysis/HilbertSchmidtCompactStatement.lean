import Langlands.Analysis.OperatorIdeals
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness of Hilbert–Schmidt operators

The statement uses the existing existential-basis predicate and Mathlib's
actual compact-operator predicate. It imposes no separability hypothesis.
-/

namespace Langlands.Analysis.OperatorIdeals

universe u v

/-- Every Hilbert–Schmidt operator between complex Hilbert spaces is compact. -/
def HilbertSchmidtCompactStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F), IsHilbertSchmidt A → IsCompactOperator A

end Langlands.Analysis.OperatorIdeals
