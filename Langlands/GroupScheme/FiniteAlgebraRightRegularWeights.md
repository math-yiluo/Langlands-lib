# Split-torus weight elements in the original finite algebra

Author: Worker 118.

Let `A` be a possibly noncommutative algebra over a field `k : Type u`,
with finite basis `b`. For an actual homomorphism from a standard split
torus to `FiniteAlgebraUnits.groupScheme b`, this module turns a universal
weight column in the inverse-right-regular representation into an element
of the original algebra.

`baseAffineUnit b` recovers an actual unit of `A` from an affine point
with coefficient algebra `k`, by the published affine unit coordinates
and the tensor unit isomorphism `k ⊗[k] A ≃ A`.

`torusCoefficientElement b I i m j` is the element whose basis coordinates
are the `j`-th universal coefficient column at exponent `m`. It is
nonzero if that column is nonzero. The main eigenvector identity says
that for every tuple `t : I → kˣ`, right multiplication by the inverse
of the actual unit represented by `i(t)` multiplies the element by
the scalar exponent monomial `t^m`.

The proof uses the published all-coefficient eigenvector identity
`GeneralLinear.CocharacterDiagonal.coefficientColumn_weight` and the
affine coordinate formula proved in the companion helper
`FiniteAlgebraRightRegularAffine`. Coordinates in the base-changed basis
give the equality in `k ⊗[k] A`, and the tensor unit map returns it to
the original algebra.

This is an internal coordinate construction. It holds in arbitrary
characteristic without centrality, simplicity, or infinitude hypotheses.
No faithfulness of the torus map, nonzero weight, or nonzero coefficient
column is assumed unless explicitly stated in the corresponding lemma.
