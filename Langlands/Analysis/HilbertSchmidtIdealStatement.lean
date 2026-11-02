import Langlands.Analysis.OperatorIdeals
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace Langlands.Analysis.OperatorIdeals

universe u v w

/-- The existential-basis Hilbert–Schmidt predicate is a complex vector space
ideal of bounded maps and is invariant under the Hilbert adjoint. -/
def HilbertSchmidtIdealStatement : Prop :=
  ∀ (E : Type u) (F : Type v) (G : Type w)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G],
    IsHilbertSchmidt (0 : E →L[ℂ] F) ∧
    (∀ (A B : E →L[ℂ] F),
      IsHilbertSchmidt A → IsHilbertSchmidt B → IsHilbertSchmidt (A + B)) ∧
    (∀ (c : ℂ) (A : E →L[ℂ] F),
      IsHilbertSchmidt A → IsHilbertSchmidt (c • A)) ∧
    (∀ (A : E →L[ℂ] F), IsHilbertSchmidt A ↔ IsHilbertSchmidt A.adjoint) ∧
    (∀ (A : E →L[ℂ] F) (B : F →L[ℂ] G),
      IsHilbertSchmidt A → IsHilbertSchmidt (B.comp A)) ∧
    (∀ (A : E →L[ℂ] F) (C : G →L[ℂ] E),
      IsHilbertSchmidt A → IsHilbertSchmidt (A.comp C))

end Langlands.Analysis.OperatorIdeals
