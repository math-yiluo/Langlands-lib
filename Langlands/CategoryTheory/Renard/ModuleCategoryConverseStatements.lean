import Langlands.CategoryTheory.Renard.SmallProjective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Equivalence

/-!
# Renard A.VIII.2: a small progenerator in a category equivalent to modules

The converse is realized by the actual inverse image of the lifted regular
unital module. Only the source category's coproducts enter the statement.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u r s

namespace Langlands.Renard

/-- The module-category converse in Renard A.VIII.2, realized by the inverse
image of the regular module under the supplied actual equivalence. -/
def ModuleCategoryConverseStatement
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : Type r) [Ring R] : Prop :=
  ∀ e : C ≌ ModuleCat.{max r s} R,
    HomSmallProgenerator.{w} (e.inverse.obj (ModuleCat.of R (ULift.{s} R)))

end Langlands.Renard
