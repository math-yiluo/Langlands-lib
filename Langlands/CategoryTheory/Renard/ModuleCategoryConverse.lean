import Langlands.CategoryTheory.Renard.ModuleCategoryConverseStatements
import Langlands.CategoryTheory.Renard.RegularModuleSmallProgenerator
import Langlands.CategoryTheory.Renard.SmallProgeneratorTransport
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Renard A.VIII.2: the module-category converse

Proof of `Langlands.Renard.ModuleCategoryConverseStatement`. Coproducts of index size `w` are
carried from `C` to the module category along the inverse of the supplied equivalence; the
published regular-module theorem then applies at that size, and the published transport theorem,
used for the inverse equivalence `e.symm`, carries the small progenerator back to `C`. See the
paired Markdown for the proof route.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe w v u r s

namespace Langlands.Renard

/-- A category with coproducts of index size `w` that is equivalent to the unital left modules
over `R` passes these coproducts to the module category, through the inverse of the
equivalence. -/
theorem hasCoproducts_moduleCat_of_equivalence
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] {R : Type r} [Ring R]
    (e : C ≌ ModuleCat.{max r s} R) : HasCoproducts.{w} (ModuleCat.{max r s} R) :=
  fun _ => Adjunction.hasColimitsOfShape_of_equivalence e.inverse

/-- Renard A.VIII.2, the converse after the equivalence theorem: in an abelian category with
coproducts of index size `w` equivalent to the unital left modules over `R`, the inverse image of
the lifted regular module is a small progenerator at that index size. -/
theorem moduleCategoryConverse
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : Type r) [Ring R] :
    ModuleCategoryConverseStatement.{w, v, u, r, s} C R := by
  intro e
  have := hasCoproducts_moduleCat_of_equivalence.{w} e
  exact (smallProgeneratorTransport.{w} (ModuleCat.{max r s} R) C e.symm
    (ModuleCat.of R (ULift.{s} R))).1 (regularModuleSmallProgenerator.{w, s, r} R)

end Langlands.Renard
