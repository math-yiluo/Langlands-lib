/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Divisibility along an exact sequence

If `f : M₁ →ₗ[R] M₂`, `g : M₂ →ₗ[R] M₃` is exact with `f` injective and `s : R` acts
regularly on `M₃`, then an element of `M₁` whose image under `f` is divisible by `s` is
itself divisible by `s`.
-/

@[expose] public section

open Pointwise

namespace Submodule

variable {R : Type*} [CommRing R]
variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- If `s` acts regularly on the third term of an exact sequence whose first map is
injective, then an element of `M₁` whose image lies in `s • M₂` already lies in `s • M₁`.
This is the hypothesis of `Submodule.torsion'QuotientMap_exact`. -/
theorem comap_smul_top_le_of_isSMulRegular {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hf : Function.Injective f) (hfg : Function.Exact f g) {s : R}
    (hs : IsSMulRegular M₃ s) :
    Submodule.comap f (s • (⊤ : Submodule R M₂)) ≤ s • (⊤ : Submodule R M₁) := by
  intro y hy
  rw [Submodule.mem_comap, mem_smul_pointwise_iff_exists] at hy
  obtain ⟨x, -, hx⟩ := hy
  have hgx : g x = 0 := by
    refine hs (?_ : s • g x = s • 0)
    rw [smul_zero, ← map_smul, hx, hfg.apply_apply_eq_zero]
  obtain ⟨z, rfl⟩ := (hfg x).mp hgx
  rw [mem_smul_pointwise_iff_exists]
  exact ⟨z, mem_top, hf (by rw [map_smul, hx])⟩

end Submodule
