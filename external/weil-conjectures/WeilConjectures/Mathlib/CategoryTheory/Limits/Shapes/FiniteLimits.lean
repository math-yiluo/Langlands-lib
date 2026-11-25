/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# FiniteLimits

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits`).
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

instance (J : Type*) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  cases nonempty_fintype J
  apply hasLimitsOfShape_of_equivalence
    (WidePullbackShape.equivalenceOfEquiv _ (Fintype.equivFin J).symm)

end CategoryTheory.Limits
