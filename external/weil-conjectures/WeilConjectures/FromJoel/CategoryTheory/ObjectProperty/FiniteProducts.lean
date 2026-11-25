/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Properties of objects that are stable under finite products

Supplement to `Mathlib.CategoryTheory.ObjectProperty.FiniteProducts`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category C] (P : ObjectProperty C)

lemma prop_biprod_of_isClosedUnderBinaryProducts
    [HasZeroMorphisms C] [P.IsClosedUnderBinaryProducts] (X Y : C)
    [HasBinaryBiproduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⊞ Y) :=
  P.prop_of_isLimit (BinaryBiproduct.isLimit X Y) (by rintro ⟨_ | _⟩ <;> assumption)

end CategoryTheory.ObjectProperty
