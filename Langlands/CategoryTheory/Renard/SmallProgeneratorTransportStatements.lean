import Langlands.CategoryTheory.Renard.SmallProjective
import Mathlib.CategoryTheory.Equivalence

/-!
# Transport of Renard's small progenerators across equivalences

This is a derived prerequisite for the module-category converse in Renard
A.VIII.2, not a separately stated result in the source. The source and target
object and Hom universes, and the coproduct index universe, are independent.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace Langlands.Renard

/-- An actual equivalence transports Renard's small-progenerator predicate
at the same coproduct index size, with independent source and target sizes. -/
def SmallProgeneratorTransportStatement
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (D : Type u') [Category.{v'} D] [Abelian D] [HasCoproducts.{w} D] : Prop :=
  ∀ (e : C ≌ D) (P : C),
    HomSmallProgenerator.{w} P ↔ HomSmallProgenerator.{w} (e.functor.obj P)

end Langlands.Renard
