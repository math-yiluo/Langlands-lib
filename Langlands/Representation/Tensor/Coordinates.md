# Coordinate realizations of full tensor representations

Author: Worker 2.

This module realizes the algebraic tensor product of two finite-coordinate
representations on the product coordinate type. It constructs a bundled
representation equivalence and proves that the transported action has the
usual Kronecker matrix. Its namespace is `Langlands.CoordinateTensor`.

## Parameters and coordinate map

Let `R : Type u` be any commutative ring, and let `n : Type v` and
`m : Type w` have `Fintype` instances. These universes are independent.
Empty coordinate types and the zero ring are allowed. The definition
`coordinates R n m` is the linear equivalence

```text
((n → R) ⊗[R] (m → R)) ≃ₗ[R] (n × m → R).
```

It is Mathlib's `Basis.equivFun` for the tensor product of the two
standard bases `Pi.basisFun R n` and `Pi.basisFun R m`. Thus its source is
the full algebraic module tensor product. `coordinates_tmul` proves

```text
coordinates (v ⊗ w) (i,j) = v(i) * w(j).
```

The proof uses the tensor-basis coordinate formula and commutativity of
multiplication. `coordinates_symm_mul` proves that the inverse sends the
function `(i,j) ↦ v(i) * w(j)` to `v ⊗ w`, by applying injectivity of the
coordinate equivalence. These formulas identify the product-index order.
They do not assert that every tensor is decomposable.

For linear endomorphisms `f` of `n → R` and `g` of `m → R`,
`coordinates_map` proves, for every tensor `x`,

```text
coordinates (TensorProduct.map f g x)
  = (toMatrix' f ⊗ₖ toMatrix' g) *ᵥ coordinates x.
```

Here `⊗ₖ` is the Kronecker product of matrices and `*ᵥ` is multiplication
on column vectors. This theorem also takes `DecidableEq n` and
`DecidableEq m` for the matrix API. Its proof reuses Mathlib's
`TensorProduct.toMatrix_map`, together with
`LinearMap.toMatrix_mulVec_repr` and the comparison of `toMatrix` in the
standard bases with `toMatrix'`. It establishes the formula on all
tensors directly through basis coordinates.

## Representation and equivalence

Let `G : Type z` be any monoid, independently of the preceding universes,
and let

```text
ρ : Representation R G (n → R)
σ : Representation R G (m → R).
```

Mathlib's `ρ.tprod σ` is the representation on the full tensor product
whose action at `a : G` is `TensorProduct.map (ρ a) (σ a)`.
The definition `representation ρ σ` transports this representation to
`n × m → R`. It composes the monoid homomorphism `ρ.tprod σ` with
`coordinates.conjRingEquiv.toMonoidHom`. Preservation of identity and
multiplication therefore comes from actual homomorphism composition.

`representation_apply` records its defining action:

```text
representation ρ σ a x
  = coordinates (TensorProduct.map (ρ a) (σ a) (coordinates.symm x)).
```

`equiv ρ σ` is a bundled `Representation.Equiv` from `ρ.tprod σ` to
`representation ρ σ`. Its underlying linear equivalence is
`coordinates`; its intertwining law follows by cancelling
`coordinates.symm (coordinates x)`. `equiv_tmul` gives its value on a
pure tensor using the same coordinate product formula.

`representation_matrix` proves that, for every coordinate vector `x`,

```text
representation ρ σ a x
  = (toMatrix' (ρ a) ⊗ₖ toMatrix' (σ a)) *ᵥ x.
```

It follows from `coordinates_map` and cancellation of the inverse
coordinate map; this matrix theorem takes decidable equality on both
index types. Finally, `representation_decomposable` proves

```text
representation ρ σ a (fun (i,j) ↦ v(i) * w(j))
  = fun (i,j) ↦ (ρ a v)(i) * (σ a w)(j).
```

Its proof uses `coordinates_symm_mul`, `TensorProduct.map_tmul`, and
`coordinates_tmul`. Neither the representation equivalence nor this
last action formula requires a group, field, nonempty index, or
separately supplied nonsingularity hypothesis.

## Provenance and scope

This is internal content derived from Mathlib's actual standard and
tensor bases, coordinate equivalences, tensor maps, tensor
representations, and conjugation of endomorphism rings. The matrix
comparison specifically reuses
`Mathlib/LinearAlgebra/TensorProduct/Matrix.lean`; the representation and
intertwining structures come from
`Mathlib/RepresentationTheory/Intertwining.lean` and its imports.
No additional correspondence with external literature is claimed.

This is the module-level coordinate comparison needed for algebraic
coefficient tensor products. It does not construct a tensor morphism
of group schemes or identify one with these representations. The
actual GL tensor scheme morphism and the adapter for two morphisms
from a common group scheme remain separate constructions. There is
no topology, analytic differentiation, arbitrary-module basis
independence, or automorphic coefficient attachment in this unit.
