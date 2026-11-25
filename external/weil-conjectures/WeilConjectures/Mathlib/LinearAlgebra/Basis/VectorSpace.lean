/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear maps between vector spaces are von Neumann regular

Every linear map `f : V → W` between vector spaces over a division ring has a *generalized
inverse* `s : W → V`, with `f ∘ s ∘ f = f` (`LinearMap.exists_comp_comp_eq_self`).
-/

@[expose] public section

namespace LinearMap

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- Every linear map `f` between vector spaces has a generalized inverse `s`, with
`f ∘ s ∘ f = f`: compose a right inverse of `V ↠ range f` with a left inverse of
`range f ↪ W`. -/
theorem exists_comp_comp_eq_self (f : V →ₗ[K] W) : ∃ s : W →ₗ[K] V, f ∘ₗ s ∘ₗ f = f := by
  obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨l, hl⟩ := (range f).subtype.exists_leftInverse_of_injective (range f).ker_subtype
  refine ⟨r ∘ₗ l, LinearMap.ext fun x ↦ ?_⟩
  have hr' (y : range f) : f (r y) = y := congr(($hr y : W))
  have hl' (y : range f) : l y = y := congr($hl y)
  have hx : f x = (f.rangeRestrict x : W) := rfl
  rw [comp_apply, comp_apply, hx, comp_apply, hl', hr']

end LinearMap
