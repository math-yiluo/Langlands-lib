/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear maps of matrices in coordinates

`Matrix.toLin b b M` is the linear map whose matrix in the basis `b` is `M`: in the coordinates
`b.equivFun`, it is multiplication by `M`.

## Main declarations

* `Matrix.toLin_apply_eq_equivFun_symm`: `toLin b b M x = b.equivFun.symm (M *ᵥ b.equivFun x)`.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {R : Type*} [CommSemiring R] {n : Type*} [Fintype n] [DecidableEq n]
  {M : Type*} [AddCommMonoid M] [Module R M]

/-- The linear map `toLin b b A` reads, in the coordinates of the basis `b`, as multiplication by
the matrix `A`. -/
theorem toLin_apply_eq_equivFun_symm (b : Module.Basis n R M) (A : Matrix n n R) (x : M) :
    toLin b b A x = b.equivFun.symm (A *ᵥ b.equivFun x) := by
  simp [toLin_apply, Module.Basis.equivFun_symm_apply]

end Matrix
