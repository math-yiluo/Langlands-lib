/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Initially small categories and universe enlargement

An initially small category stays initially small when the universe parameter is enlarged.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

/-- A `w`-initially small category is `max w w'`-initially small. -/
theorem initiallySmall_lift (J : Type u) [Category.{v} J] [InitiallySmall.{w} J] :
    InitiallySmall.{max w w'} J :=
  have : Small.{max w w'} (InitialModel.{w} J) := small_lift.{w, w'} _
  initiallySmall_of_initial_of_essentiallySmall (fromInitialModel.{w} J)

end CategoryTheory
