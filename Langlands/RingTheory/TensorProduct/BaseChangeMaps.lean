module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Values of base-change maps on pure tensors

The natural map `A ⊗[R] (M →ₗ[R] N) → (A ⊗[R] M →ₗ[A] A ⊗[R] N)` sends `a ⊗ f` to `a` times the
base change of `f` (`LinearMap.tensorProduct_tmul`, and `LinearMap.tensorProductEnd_tmul` for
endomorphisms); these are `simp` lemmas of high priority, so that Mathlib's `LinearMap.baseChange`
lemmas apply after them. Multiplication on a tensor square is natural in the algebra
(`Algebra.TensorProduct.lmul'_map_self`).
-/

public section

open TensorProduct

/-- The natural map `A ⊗[R] (M →ₗ[R] N) → (A ⊗[R] M →ₗ[A] A ⊗[R] N)` sends `a ⊗ f` to
`a • f.baseChange A`. -/
@[simp high]
theorem LinearMap.tensorProduct_tmul {R A M N : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (a : A)
    (f : M →ₗ[R] N) : LinearMap.tensorProduct R A M N (a ⊗ₜ f) = a • f.baseChange A :=
  rfl

/-- The natural algebra map `A ⊗[R] Module.End R M → Module.End A (A ⊗[R] M)` sends `a ⊗ f` to
`a • f.baseChange A`. -/
@[simp high]
theorem LinearMap.tensorProductEnd_tmul {R A M : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] (a : A) (f : Module.End R M) :
    LinearMap.tensorProductEnd R A M (a ⊗ₜ f) = a • f.baseChange A :=
  rfl

namespace Algebra.TensorProduct

/-- Multiplication on a tensor square commutes with an algebra map applied to both factors. -/
@[simp]
theorem lmul'_map_self {R A C : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring C] [Algebra R A] [Algebra R C] (f : A →ₐ[R] C) (x : A ⊗[R] A) :
    lmul' R (map f f x) = f (lmul' R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

end Algebra.TensorProduct
