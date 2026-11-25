/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The right orthogonal is closed under limits

In a preadditive category, the right orthogonal of any property of objects is closed under
limits of any shape.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

/-- The right orthogonal of a property of objects of a preadditive category is closed under
limits: a morphism into a limit vanishes if its composites with the projections do. -/
instance isClosedUnderLimitsOfShape_rightOrthogonal {C : Type*} [Category C] [Preadditive C]
    (P : ObjectProperty C) (J : Type*) [Category J] :
    P.rightOrthogonal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le X := by
    rintro ⟨h⟩ Y f hY
    refine h.isLimit.hom_ext fun j ↦ ?_
    rw [Limits.zero_comp]
    exact h.prop_diag_obj j (f ≫ h.π.app j) hY

end CategoryTheory.ObjectProperty
