/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Sheaves with values in a category killed by an integer

If an integer `N` kills every object of a preadditive category `A`, then it kills every sheaf
with values in `A`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {A : Type*} [Category A]
  [Preadditive A]

/-- If `N • 𝟙 M = 0` for every object `M` of `A`, then `N • 𝟙 F = 0` for every `A`-valued
sheaf `F`: this holds on sections. -/
lemma nsmul_id_eq_zero_of_forall {N : ℕ} (h : ∀ M : A, N • 𝟙 M = 0) (F : Sheaf J A) :
    N • 𝟙 F = 0 :=
  (sheafToPresheaf J A).map_injective (by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
    ext U
    simp only [NatTrans.app_nsmul, NatTrans.id_app, NatTrans.app_zero, h])

end CategoryTheory.Sheaf
