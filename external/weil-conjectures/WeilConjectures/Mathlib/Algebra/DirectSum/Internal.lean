/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.DirectSum.Internal

/-!
# The degree-zero part of an internally graded algebra is a scalar tower

For an internally graded `S`-algebra `𝒜 : ι → Submodule S R`, Mathlib provides both
`SetLike.GradeZero.instAlgebra : Algebra S (𝒜 0)` and the algebra structure of `R` over
`𝒜 0`, but not the compatibility of the two, which is needed to transport
`Algebra.FiniteType S R` to `Algebra.FiniteType (𝒜 0) R`.
-/

@[expose] public section

namespace SetLike.GradeZero

variable {ι S R : Type*} [CommSemiring S] [CommSemiring R] [Algebra S R] [AddMonoid ι]
variable (𝒜 : ι → Submodule S R) [SetLike.GradedMonoid 𝒜]

/-- The base ring, the degree-zero part and the whole ring of an internally graded algebra
form a scalar tower: both composites `S → 𝒜 0 → R` and `S → R` are the algebra map. -/
instance isScalarTower : IsScalarTower S (𝒜 0) R :=
  IsScalarTower.of_algebraMap_eq fun s ↦ (SetLike.GradeZero.coe_algebraMap 𝒜 s).symm

end SetLike.GradeZero
