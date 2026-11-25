/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Complements on subrings

* `Subring.inv_mem_of_isUnit`: if an element of a subring of a division ring is a unit of
  that subring, then its inverse in the ambient ring already lies in the subring.
* `Subring.closure_image_eq_top`: the image of a generating set under a surjective ring
  homomorphism generates the target.
-/

@[expose] public section

namespace Subring

variable {K : Type*} [DivisionRing K] (S : Subring K)

/-- The inverse of an element of a subring of a division ring which is a unit of the
subring belongs to the subring. -/
theorem inv_mem_of_isUnit {x : K} (hx : x ∈ S) (hu : IsUnit (⟨x, hx⟩ : S)) : x⁻¹ ∈ S := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  have hxy : x * (y : K) = 1 := congrArg Subtype.val hy
  rw [inv_eq_of_mul_eq_one_right hxy]
  exact y.2

/-- If `s` generates `A` as a ring and `f : A →+* B` is surjective, then the image of `s`
generates `B`. -/
theorem closure_image_eq_top {A B : Type*} [Ring A] [Ring B] (f : A →+* B)
    (hf : Function.Surjective f) {s : Set A} (hs : Subring.closure s = ⊤) :
    Subring.closure (f '' s) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := hf x
  exact Subring.mem_closure_image_of f (hs ▸ Subring.mem_top y)

end Subring
