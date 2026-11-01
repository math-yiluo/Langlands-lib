import Langlands.AlgebraicGeometry.Picard.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# The contravariant scheme Picard group functor

Pullback uses the canonical strong monoidal structure from the Library.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.Picard.Group

section Laws

variable (X : Scheme.{u})

lemma pullback_id :
    pullback (𝟙 X) = AddMonoidHom.id (Group X) := by
  apply AddMonoidHom.ext
  intro x
  change pullback (𝟙 X) x = x
  rw [← classOf_representative X x, pullback_classOf]
  exact (classOf_eq_iff X _ _).mpr ⟨(Scheme.Modules.pullbackId X).app _⟩

variable {X} {Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)

lemma pullback_comp : pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  apply AddMonoidHom.ext
  intro x
  change pullback (f ≫ g) x = pullback f (pullback g x)
  rw [← classOf_representative Z x, pullback_classOf, pullback_classOf,
    pullback_classOf]
  exact (classOf_eq_iff X _ _).mpr ⟨((Scheme.Modules.pullbackComp f g).app _).symm⟩

end Laws

/-- Pullback makes the scheme Picard group contravariantly functorial. -/
def functor : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj X := AddCommGrpCat.of (Group X.unop)
  map f := AddCommGrpCat.ofHom (pullback f.unop)
  map_id X := by
    change AddCommGrpCat.ofHom (pullback (𝟙 X.unop)) = _
    rw [pullback_id]
    rfl
  map_comp f g := by
    change AddCommGrpCat.ofHom (pullback (g.unop ≫ f.unop)) = _
    rw [pullback_comp]
    rfl

end Langlands.AlgebraicGeometry.Picard.Group
