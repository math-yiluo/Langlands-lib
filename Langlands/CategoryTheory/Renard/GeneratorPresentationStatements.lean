import Langlands.CategoryTheory.Renard.HomObjectProperties
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Presentations by two coproducts of a generator

A strengthened statement of the final lemma of Renard A.VIII.2. The actual
right-exact row uses coproducts indexed in the Hom universe; its construction
and proof are separate obligations.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every object has a right-exact presentation by two coproducts of copies
of a generator, assuming coproducts at the size of the Hom types. -/
def GeneratorPresentationStatement [HasCoproducts.{v} C] (P : C) : Prop :=
  HomGenerator P →
    ∀ M : C, ∃ (I J : Type v)
      (f : (∐ fun _ : J => P) ⟶ (∐ fun _ : I => P))
      (g : (∐ fun _ : I => P) ⟶ M)
      (h : f ≫ g = 0),
      (ShortComplex.mk f g h).Exact ∧ Epi g

end Langlands.Renard
