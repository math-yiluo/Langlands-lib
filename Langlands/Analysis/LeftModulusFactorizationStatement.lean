import Langlands.Analysis.OperatorIdeals

/-!
# Contractive factorization through the positive left modulus
-/

namespace Langlands.Analysis.OperatorIdeals

universe u

/-- Every bounded complex Hilbert-space endomorphism factors through its
positive left modulus on the left, with a contractive right factor. -/
def LeftModulusFactorizationStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E),
    ∃ U : E →L[ℂ] E, ‖U‖ ≤ 1 ∧ A = (leftModulus A).comp U

end Langlands.Analysis.OperatorIdeals
