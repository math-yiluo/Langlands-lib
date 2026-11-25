/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Intersections of tensor products of subspaces

For subspaces `I ≤ A` and `J ≤ B` of vector spaces over a field, `(I ⊗ B) ∩ (A ⊗ J) = I ⊗ J`
inside `A ⊗ B`.

## Main statements

- `LinearMap.range_rTensor_inf_range_lTensor`: `(I ⊗ B) ⊓ (A ⊗ J) = I ⊗ J`.
-/

@[expose] public section

open TensorProduct

namespace LinearMap

variable {K A B : Type*} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- **Intersection of tensor products of subspaces.** For subspaces `I ≤ A` and `J ≤ B` of vector
spaces over a field, `(I ⊗ B) ⊓ (A ⊗ J) = I ⊗ J` inside `A ⊗ B`: projecting along complements
of `I` and of `J` fixes every element of the intersection and lands in `I ⊗ J`. -/
theorem range_rTensor_inf_range_lTensor (I : Submodule K A) (J : Submodule K B) :
    range (I.subtype.rTensor B) ⊓ range (J.subtype.lTensor A) =
      range (TensorProduct.map I.subtype J.subtype) := by
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · rintro _ ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    obtain ⟨p, hp⟩ := I.subtype.exists_leftInverse_of_injective I.ker_subtype
    obtain ⟨q, hq⟩ := J.subtype.exists_leftInverse_of_injective J.ker_subtype
    have h1 : ((I.subtype ∘ₗ p).rTensor B) (I.subtype.rTensor B y) = I.subtype.rTensor B y := by
      rw [← LinearMap.comp_apply, ← rTensor_comp, comp_assoc, hp, comp_id]
    have h2 : ((J.subtype ∘ₗ q).lTensor A) (I.subtype.rTensor B y) =
        I.subtype.rTensor B y := by
      rw [← hz, ← LinearMap.comp_apply, ← lTensor_comp, comp_assoc, hq, comp_id]
    refine ⟨TensorProduct.map p q (I.subtype.rTensor B y), ?_⟩
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← rTensor_comp_lTensor,
      LinearMap.comp_apply, h2, h1]
  · rintro _ ⟨y, rfl⟩
    exact ⟨J.subtype.lTensor I y, by rw [← LinearMap.comp_apply, rTensor_comp_lTensor]⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨I.subtype.rTensor J y, by rw [← LinearMap.comp_apply, lTensor_comp_rTensor]⟩

end LinearMap
