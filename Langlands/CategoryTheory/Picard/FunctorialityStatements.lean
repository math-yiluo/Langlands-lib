import Langlands.CategoryTheory.Picard.Basic

/-!
# Functoriality statements for the categorical Picard group

These proposition definitions state identity, composition, and invariance under
an ordinary natural isomorphism for the induced additive homomorphisms.
-/

open CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace Langlands.CategoryTheory.PicardGroup

/-- The identity strong monoidal functor induces the identity Picard homomorphism. -/
def MapIdentityStatement
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C] : Prop :=
  map (𝟭 C) = AddMonoidHom.id (PicardGroup C)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Composition of strong monoidal functors induces composition of Picard homomorphisms. -/
def MapCompositionStatement [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] : Prop :=
  map (F ⋙ G) = (map G).comp (map F)

/-- An ordinary natural isomorphism suffices for equality of Picard homomorphisms. -/
def MapIsoStatement [BraidedCategory C] [BraidedCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] : Prop :=
  ∀ (_ : F ≅ G), map F = map G

end Langlands.CategoryTheory.PicardGroup
