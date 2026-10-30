import Langlands.CategoryTheory.Renard.SmallProjective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.ULift

/-!
# Renard A.VIII.2: the regular unital module is a small progenerator

The category is Mathlib's category of unital left modules over an arbitrary
unital ring, and the object is the regular module lifted to the carrier universe.
The ring, carrier and coproduct index universes are independent; coproduct
existence at the index size is an explicit hypothesis. This module states the
assertion; it contains no proof of it.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Langlands.Renard

/-- Renard A.VIII.2, remark after the equivalence theorem: a unital ring is a
small progenerator of its category of unital left modules, at coproduct index
size `w`, with the regular module lifted to the carrier universe `max u v`. -/
def RegularModuleSmallProgeneratorStatement (R : Type u) [Ring R]
    [HasCoproducts.{w} (ModuleCat.{max u v} R)] : Prop :=
  HomSmallProgenerator.{w} (ModuleCat.of R (ULift.{v} R))

end Langlands.Renard
