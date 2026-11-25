/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Exact functors: accessors

Supplement to `Mathlib.CategoryTheory.Limits.ExactFunctor`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D]

lemma exactFunctor.preservesFiniteLimits {F : C ⥤ D} (hF : exactFunctor _ _ F) :
    PreservesFiniteLimits F := hF.1

lemma exactFunctor.preservesFiniteColimits {F : C ⥤ D} (hF : exactFunctor _ _ F) :
    PreservesFiniteColimits F := hF.2

end CategoryTheory
