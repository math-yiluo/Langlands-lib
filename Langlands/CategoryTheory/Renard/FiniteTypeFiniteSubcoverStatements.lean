import Langlands.CategoryTheory.RenardFiniteType

/-!
# Renard A.I.3: finite type and finite subcovers

Source: Renard, French edition dated 9 July 2026, A.I.3,
printed pages 248–249 / PDF254–255. This module only defines a proposition.
-/

universe u v

open CategoryTheory

namespace Langlands.Renard

/-- The nonempty proper-chain finite-type condition is equivalent to the
finite-subcover condition, using the published union-existence conjuncts. -/
def FiniteTypeFiniteSubcoverStatement (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, IsFiniteTypeObject X ↔ HasFiniteSubcoverProperty X

end Langlands.Renard
