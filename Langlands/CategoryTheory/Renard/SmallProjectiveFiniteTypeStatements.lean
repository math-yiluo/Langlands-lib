import Langlands.CategoryTheory.Renard.SmallProjective
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Langlands.CategoryTheory.RenardFiniteType

/-!
# Small projectives and finite-type projectives in Renard's Grothendieck categories

The source coproduct index universe is independent of the Hom and object
universes. Objectwise smallness of the full subobject type discloses the size
presupposition for the comparison with the all-subsets finite-type predicate.
This module states the comparison; it contains no proof of it.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Langlands.Renard

/-- Renard A.VIII.2: in a source Grothendieck category, small projectivity is
projectivity together with finite type, at an explicit subobject indexing size. -/
def SmallProjectiveFiniteTypeStatement (C : Type u) [Category.{v} C] [Abelian C] :
    Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C,
    letI : HasCoproducts.{w} C := hG.1
    ∀ (P : C) [Small.{w} (Subobject P)],
      HomSmallProjective.{w} P ↔ HomProjective P ∧ IsFiniteTypeObject P

end Langlands.Renard
