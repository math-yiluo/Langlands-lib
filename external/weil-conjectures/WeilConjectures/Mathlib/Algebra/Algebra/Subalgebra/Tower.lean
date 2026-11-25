/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Scalar towers of nested subalgebras

For subalgebras `S ≤ T` of `A`, making `T` an `S`-algebra via `Subalgebra.inclusion` gives a
scalar tower `S → T → A` (`Subalgebra.isScalarTower_inclusion`).

Proving this once for arbitrary `S` and `T` keeps the kernel from unfolding concrete
subalgebras such as `Algebra.adjoin R s` when it checks the tower.
-/

public section

/-- For subalgebras `S ≤ T` of `A`, with `T` made an `S`-algebra via `Subalgebra.inclusion`,
the algebras `S → T → A` form a scalar tower.

This is the `.toAlgebra` form of the scoped instance `Subalgebra.inclusion.isScalarTower_right`
(with `X := A`), which is stated for `(Subalgebra.inclusion h).toModule`. -/
theorem Subalgebra.isScalarTower_inclusion {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {S T : Subalgebra R A} (h : S ≤ T) :
    letI := (Subalgebra.inclusion h).toAlgebra
    IsScalarTower S T A :=
  letI := (Subalgebra.inclusion h).toAlgebra
  .of_algebraMap_eq fun _ ↦ rfl
