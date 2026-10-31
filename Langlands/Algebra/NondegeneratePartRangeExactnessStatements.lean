import Langlands.Algebra.NonUnitalModuleKernels

/-!
# Range-kernel exactness after restriction to the nondegenerate parts

Renard I.1.2, printed p.8/PDF14, proves preservation of exactness by
lifting through an idempotent that fixes the given middle vector.
This file states that original-map assertion and does not prove it.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uL uM uN

/-- Equality of the actual stable range and kernel is preserved by the
published restriction of original intertwiners to their nondegenerate parts. -/
def NondegeneratePartRangeExactnessStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (L : Type uL) (M : Type uM) (N : Type uN)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A L] [NonUnitalModule A M] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A L M) (g : NonUnitalModuleHom A M N),
    f.rangeSubmodule = g.kernelSubmodule →
      (f.restrictNondegeneratePart hA).rangeSubmodule =
        (g.restrictNondegeneratePart hA).kernelSubmodule

/-! Complete closed interfaces at independent universes and unequal sizes. -/

example : Prop := NondegeneratePartRangeExactnessStatement.{uA, uL, uM, uN}

example : NondegeneratePartRangeExactnessStatement.{uA, uL, uM, uN} =
    (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A)
    (L : Type uL) (M : Type uM) (N : Type uN)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A L] [NonUnitalModule A M] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A L M) (g : NonUnitalModuleHom A M N),
    f.rangeSubmodule = g.kernelSubmodule →
      (f.restrictNondegeneratePart hA).rangeSubmodule =
        (g.restrictNondegeneratePart hA).kernelSubmodule) := rfl

example : NondegeneratePartRangeExactnessStatement.{0, 1, 0, 1} =
    (∀ (A : Type) [NonUnitalRing A] (hA : IsIdempotented A)
    (L : Type 1) (M : Type) (N : Type 1)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A L] [NonUnitalModule A M] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A L M) (g : NonUnitalModuleHom A M N),
    f.rangeSubmodule = g.kernelSubmodule →
      (f.restrictNondegeneratePart hA).rangeSubmodule =
        (g.restrictNondegeneratePart hA).kernelSubmodule) := rfl

example : NondegeneratePartRangeExactnessStatement.{1, 0, 1, 0} =
    (∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A)
    (L : Type) (M : Type 1) (N : Type)
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A L] [NonUnitalModule A M] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A L M) (g : NonUnitalModuleHom A M N),
    f.rangeSubmodule = g.kernelSubmodule →
      (f.restrictNondegeneratePart hA).rangeSubmodule =
        (g.restrictNondegeneratePart hA).kernelSubmodule) := rfl

end Langlands.Algebra
