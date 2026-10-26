import Langlands.CategoryTheory.Picard.TensorEquivalenceStatement

/-!
# Cancellation for a tensor of morphisms from the unit

This internal categorical statement supports the unit-pairing route to
Stacks Project Lemma 17.25.4.
-/

universe v u

open CategoryTheory MonoidalCategory

namespace Langlands.CategoryTheory.Picard

/-- If the tensor of two morphisms from the unit is an isomorphism, then both
morphisms are isomorphisms. -/
def UnitTensorCancellationStatement
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] : Prop :=
  ∀ (M N : C) (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N),
    IsIso (s ⊗ₘ t) → IsIso s ∧ IsIso t

end Langlands.CategoryTheory.Picard
