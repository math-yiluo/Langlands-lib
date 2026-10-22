import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Tensor inverses and equivalences

This statement isolates the categorical part of Stacks Project Lemma 17.25.2.
-/

universe v u

open CategoryTheory MonoidalCategory

namespace Langlands.CategoryTheory.Picard

/-- In a braided monoidal category, an object has a right tensor inverse exactly
when tensoring on the left with that object is an equivalence. -/
def TensorInvertibilityEquivalenceStatement
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] : Prop :=
  ∀ L : C, (∃ N : C, Nonempty (L ⊗ N ≅ 𝟙_ C)) ↔ (tensorLeft L).IsEquivalence

end Langlands.CategoryTheory.Picard
