import Langlands.Algebra.NonUnitalModuleAmbientAbelianProof
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Closure statements for nondegenerate original modules

Renard I.1.2, printed p.7/PDF13, asserts submodule and quotient closure.
Zero containment and finite-product closure are the explicit additional
obligations needed for the subsequent abelian-subcategory construction.
This file states all four properties and does not prove them.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uM

/-- The actual nondegenerate object property contains zero and is closed under
ambient subobjects, quotients and finite products over every idempotented ring.
No closure certificate is an input, and no original unit-action law is added. -/
def NondegenerateModuleClosureStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
    (nondegenerateProperty.{uA, uM} A).ContainsZero ∧
    (nondegenerateProperty.{uA, uM} A).IsClosedUnderSubobjects ∧
    (nondegenerateProperty.{uA, uM} A).IsClosedUnderQuotients ∧
    (nondegenerateProperty.{uA, uM} A).IsClosedUnderFiniteProducts

/-! Complete closed interfaces and both unequal ring/carrier universes. -/

example : Prop := NondegenerateModuleClosureStatement.{uA, uM}

example : NondegenerateModuleClosureStatement.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
      (nondegenerateProperty.{uA, uM} A).ContainsZero ∧
      (nondegenerateProperty.{uA, uM} A).IsClosedUnderSubobjects ∧
      (nondegenerateProperty.{uA, uM} A).IsClosedUnderQuotients ∧
      (nondegenerateProperty.{uA, uM} A).IsClosedUnderFiniteProducts) := rfl

example : NondegenerateModuleClosureStatement.{0, 1} =
    (∀ (A : Type) [NonUnitalRing A], IsIdempotented A →
      (nondegenerateProperty.{0, 1} A).ContainsZero ∧
      (nondegenerateProperty.{0, 1} A).IsClosedUnderSubobjects ∧
      (nondegenerateProperty.{0, 1} A).IsClosedUnderQuotients ∧
      (nondegenerateProperty.{0, 1} A).IsClosedUnderFiniteProducts) := rfl

example : NondegenerateModuleClosureStatement.{1, 0} =
    (∀ (A : Type 1) [NonUnitalRing A], IsIdempotented A →
      (nondegenerateProperty.{1, 0} A).ContainsZero ∧
      (nondegenerateProperty.{1, 0} A).IsClosedUnderSubobjects ∧
      (nondegenerateProperty.{1, 0} A).IsClosedUnderQuotients ∧
      (nondegenerateProperty.{1, 0} A).IsClosedUnderFiniteProducts) := rfl

end Langlands.Algebra
