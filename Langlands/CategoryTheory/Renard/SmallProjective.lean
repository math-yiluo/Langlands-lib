import Langlands.CategoryTheory.Renard.HomObjectProperties
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Renard's small projectives and small progenerators

Smallness is preservation of coproducts by the actual integer-module Hom
functor. The indexing universe is independent of the object and Hom universes.
Each predicate retains the existence of coproducts at that indexing size.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual covariant integer-module Hom functor preserves every coproduct
whose index type is in `Type w`. -/
def HomPreservesCoproducts [HasCoproducts.{w} C] (P : C) : Prop :=
  ∀ I : Type w,
    PreservesColimitsOfShape (Discrete I)
      (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

/-- Renard's small projective: a projective object whose Hom functor preserves
coproducts at the specified indexing size. -/
def HomSmallProjective [HasCoproducts.{w} C] (P : C) : Prop :=
  HomProjective P ∧ HomPreservesCoproducts.{w} P

/-- Renard's small progenerator at the specified coproduct indexing size. -/
def HomSmallProgenerator [HasCoproducts.{w} C] (P : C) : Prop :=
  HomSmallProjective.{w} P ∧ HomGenerator P

/-- Definitional unfolding of Hom coproduct preservation. -/
theorem homPreservesCoproducts_iff [HasCoproducts.{w} C] (P : C) :
    HomPreservesCoproducts.{w} P ↔
      ∀ I : Type w,
        PreservesColimitsOfShape (Discrete I)
          (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P) :=
  Iff.rfl

/-- Definitional unfolding of Renard's small-projective condition. -/
theorem homSmallProjective_iff [HasCoproducts.{w} C] (P : C) :
    HomSmallProjective.{w} P ↔ HomProjective P ∧ HomPreservesCoproducts.{w} P :=
  Iff.rfl

/-- Definitional unfolding of Renard's small-progenerator condition. -/
theorem homSmallProgenerator_iff [HasCoproducts.{w} C] (P : C) :
    HomSmallProgenerator.{w} P ↔ HomSmallProjective.{w} P ∧ HomGenerator P :=
  Iff.rfl

end Langlands.Renard
