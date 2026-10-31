import Langlands.CategoryTheory.Renard.SmallProjective
import Mathlib.CategoryTheory.Equivalence

/-!
# Renard's small-progenerator equivalence theorem

The conclusion concerns the actual endomorphism-module-valued Hom functor.
The coproduct indexing size and target module-carrier size are the Hom universe;
the source object universe remains independent.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Langlands.Renard

/-- Renard A.VIII.2: a small progenerator makes the actual Hom functor an
equivalence with unital right modules over its endomorphism ring. -/
def SmallProgeneratorEquivalenceStatement (C : Type u) [Category.{v} C]
    [Abelian C] [HasCoproducts.{v} C] : Prop :=
  ∀ P : C, HomSmallProgenerator.{v} P →
    (preadditiveCoyonedaObj P : C ⥤ ModuleCat.{v} (End P)ᵐᵒᵖ).IsEquivalence

end Langlands.Renard
