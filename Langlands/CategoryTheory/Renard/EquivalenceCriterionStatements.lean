import Mathlib.CategoryTheory.Equivalence

/-!
# Renard A.II.2: the equivalence criterion

The source's fully faithful and essentially surjective hypotheses are
written as properties of the actual Hom maps and actual object isomorphisms.
The conclusion supplies an actual quasi-inverse functor and both natural
isomorphisms. This module states the criterion without proving it.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace Langlands.Renard

/-- Renard A.II.2, printed page 251 / PDF257: a fully faithful functor whose
essential image contains every target object has a quasi-inverse.
The identity categories in the printed definition are corrected by typing;
the source and target object and Hom universes remain independent. -/
@[pp_with_univ]
def EquivalenceCriterionStatement
    (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] : Prop :=
  ∀ F : C ⥤ D,
    (∀ X Y : C,
      Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) →
    (∀ X Y : C,
      Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) →
    (∀ Y : D, ∃ X : C, Nonempty (F.obj X ≅ Y)) →
    ∃ G : D ⥤ C,
      Nonempty (F ⋙ G ≅ 𝟭 C) ∧ Nonempty (G ⋙ F ≅ 𝟭 D)

end Langlands.Renard
