# Products of finite free algebras of uniform rank

Author: Worker 105.

Helper module (pure algebra) for the proof of Conrad's Proposition 5.2,
`Langlands.Global.AdelicSpaceLevelPointsStatement`. It contains no statement from the
literature.

Throughout, `A i → B i` (`i : ι`) is a family of ring maps; `∏ B i` is an `∏ A i`-algebra
componentwise (Mathlib's `Pi.instAlgebraForall`).

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsDescent`.

- `piBasis b`: for modules `M i` over `A i` with bases `b i` indexed by the same `Fin d`, the
  basis of `∏ M i` over `∏ A i` whose `k`-th vector is `fun i => b i k` (`piBasis_apply`). It is
  built with `Basis.ofEquivFun` from the coordinate map `y ↦ (k ↦ (i ↦ (b i).repr (y i) k))`.
- `TensorSquares A B = ∀ i, B i ⊗[A i] B i`, with the left and right inclusions
  `inl, inr : ∏ B i →ₐ[∏ A i] TensorSquares A B`, `y ↦ (y i ⊗ 1)` and `y ↦ (1 ⊗ y i)`.
- `comparison A B : (∏ B i) ⊗[∏ A i] (∏ B i) →ₐ TensorSquares A B`, the map
  `x ⊗ y ↦ (x i ⊗ y i)` (Mathlib's `Algebra.TensorProduct.productMap` of `inl` and `inr`;
  `comparison_tmul`).
- `comparison_bijective b`: if every `B i` is free over `A i` with a basis `b i` indexed by
  `Fin d`, the comparison map is bijective. Over the left factor `∏ B i`, the source has the
  basis `1 ⊗ (piBasis b k)` (Mathlib's `Algebra.TensorProduct.basis`). The target has the basis
  `piBasis` of the bases `1 ⊗ b i k` of the `B i ⊗ B i` over `B i`. The comparison map is
  linear over the left factor and sends the first basis to the second, so it is the
  isomorphism `Basis.equiv` between them.
