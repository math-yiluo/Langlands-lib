/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-! # Scalars becoming units in an algebra

If `r : R` maps to a unit of an `R`-algebra `A`, then multiplication by `r` is injective on
every `A`-module which is a scalar tower over `R`
(`eq_zero_of_smul_eq_zero_of_isUnit_algebraMap`).
-/

@[expose] public section

/-- Multiplication by an element of `R` that becomes a unit in `A` is injective on any
`A`-module that is a scalar tower over `R`. -/
theorem eq_zero_of_smul_eq_zero_of_isUnit_algebraMap {R A P : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P] {r : R}
    (hr : IsUnit (algebraMap R A r)) {y : P} (hy : r • y = 0) : y = 0 := by
  rwa [← algebraMap_smul A r y, hr.smul_eq_zero] at hy
