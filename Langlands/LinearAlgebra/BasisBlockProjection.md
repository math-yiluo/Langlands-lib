# Block projections of a basis

Authors: Worker 187.

The module `Langlands.LinearAlgebra.BasisBlockProjection` (namespace
`Langlands.LinearAlgebra.BasisBlockProjection`) gives elementary linear algebra for a
basis whose index set is partitioned into blocks. It is an internal helper for
`Langlands.GroupScheme.CharacterBlockKernelGeneration`. It has no literature source.

## Setting

`R` is a commutative ring, `X` an `R`-module with basis `b : Module.Basis I R X`, and
`θ : I → A` assigns each basis index to a block.

## Definition

- `proj b θ α : X →ₗ[R] X` is the projection onto the span of the basis vectors in
  block `α`, along the other basis vectors. It is defined by `Module.Basis.constr`,
  sending `b i` to `b i` when `θ i = α` and to `0` otherwise.

## Results

- `proj_basis`: `proj b θ α (b i) = if θ i = α then b i else 0`. This is the
  defining property.
- `repr_proj`: the `i`-th coordinate of `proj b θ α x` is the `i`-th coordinate of
  `x` when `θ i = α`, and `0` otherwise. Proof: both sides are linear in `x` and agree
  on the basis vectors (`Module.Basis.ext`).
- `sum_proj`: if a finite set `s` contains every block `θ i`, then
  `∑ α ∈ s, proj b θ α x = x`. Proof: compare coordinates using `repr_proj` and
  `Finset.sum_ite_eq`.
- `proj_eq_zero_iff`: `proj b θ α x = 0` exactly when every coordinate of `x` in
  block `α` vanishes.
- `proj_comm`: let `g : X →ₗ[R] X` preserve, for each block `α`, the property "all
  coordinates in block `α` vanish". Then `g` commutes with every block projection.
  Proof: write `x = y + (x - y)` with `y = proj b θ α x`. The coordinates of `x - y`
  in block `α` vanish, so those of `g (x - y)` do too, and
  `proj (g (x - y)) = 0`. The coordinates of `y` in every other block `α'` vanish, so
  those of `g y` do too, so `g y` lies in block `α` and `proj (g y) = g y`. Hence
  `proj (g x) = g y`.
