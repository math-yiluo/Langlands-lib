import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert–Schmidt basis independence

This is a proposition target for bounded operators between complex Hilbert
spaces. The squared-image sums and their summability must be independent
of the domain Hilbert basis.
-/

namespace Langlands.Analysis.OperatorIdeals

universe u v w z

variable (E : Type u) (F : Type v) (ι : Type w) (κ : Type z)
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Changing the domain Hilbert basis preserves square summability and,
when summable, the squared-image sum. -/
def HilbertSchmidtBasisIndependenceStatement : Prop :=
  ∀ (A : E →L[ℂ] F) (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E),
    (Summable (fun i => ‖A (b i)‖ ^ 2) ↔ Summable (fun j => ‖A (c j)‖ ^ 2)) ∧
      (Summable (fun i => ‖A (b i)‖ ^ 2) →
        (∑' i, ‖A (b i)‖ ^ 2) = ∑' j, ‖A (c j)‖ ^ 2)

end Langlands.Analysis.OperatorIdeals
