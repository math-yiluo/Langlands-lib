/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicTopology.CechNerve

/-!
# The diagonal into the terms of a Čech nerve

For an arrow `f : X ⟶ Y`, every term `X ×_Y ⋯ ×_Y X` of the Čech nerve of `f` receives the
diagonal morphism from `X` (`CategoryTheory.Arrow.cechNerveDiagonal`). In particular no term of
the Čech nerve of a covering by a nonempty object is empty: the Čech hypercover of a single
covering cannot be truncated.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Arrow

variable {C : Type*} [Category* C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

/-- The diagonal `X ⟶ X ×_Y ⋯ ×_Y X` into the `n`-th term of the Čech nerve of `f : X ⟶ Y`. -/
noncomputable def cechNerveDiagonal (n : SimplexCategoryᵒᵖ) : f.left ⟶ f.cechNerve.obj n :=
  WidePullback.lift f.hom (fun _ ↦ 𝟙 _) (by simp)

@[reassoc (attr := simp)]
lemma cechNerveDiagonal_π (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    f.cechNerveDiagonal n ≫ WidePullback.π _ i = 𝟙 _ :=
  WidePullback.lift_π _ _ _ _ _

end CategoryTheory.Arrow
