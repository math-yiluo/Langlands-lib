/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Preserving terminal objects

A functor sending some terminal object to a terminal object preserves terminal objects.

## Main results

- `CategoryTheory.Limits.preservesLimit_empty_of_isTerminal`.
-/

@[expose] public section

namespace CategoryTheory.Limits

/-- A functor sending some terminal object to a terminal object preserves terminal objects. -/
lemma preservesLimit_empty_of_isTerminal {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {X : C} (hX : IsTerminal X) (hGX : IsTerminal (G.obj X)) :
    PreservesLimit (Functor.empty.{0} C) G :=
  preservesLimit_of_preserves_limit_cone hX ((isLimitMapConeEmptyConeEquiv G X).symm hGX)

end CategoryTheory.Limits
