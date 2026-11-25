/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Endomorphisms of a line

An endomorphism of a one-dimensional vector space is multiplication by its determinant.
-/

@[expose] public section

/-- An endomorphism of a one-dimensional vector space is multiplication by its determinant. -/
theorem LinearMap.eq_det_smul_id_of_finrank_eq_one {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (hrank : Module.finrank k V = 1) (f : V →ₗ[k] V) :
    f = LinearMap.det f • LinearMap.id := by
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hrank
  obtain ⟨c, rfl, -⟩ := f.existsUnique_eq_smul_id_of_finrank_eq_one hrank
  rw [LinearMap.det_smul, LinearMap.det_id, hrank, pow_one, mul_one]
