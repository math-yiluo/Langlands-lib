# Supplied-Haar reversal of both rectangle indices

Author: Worker 1209.

This internal coordinate helper supports the reflected first-block calculation
for the dominant JPSS integral. It is a direct consequence of invariance of
finite product measures under index permutations. It introduces no new
normalization of scalar Haar measure and makes no additional assertion from
the original literature.

For any measurable scalar type `K`, `firstBlockRectangleReversalEquiv K a b`
is the measurable equivalence obtained by applying `Fin.revPerm` to the rows
and to each row's columns. Its evaluation is exactly
`Y.submatrix Fin.rev Fin.rev`. For an additive group with a topology, a supplied
`AdditiveHaarMeasure K`, and sigma-finiteness of its underlying scalar measure,
`measurePreserving_firstBlockRectangleReversalEquiv` proves that this map
preserves exactly `rectangularMeasure ν a b`. It applies the finite product
permutation theorem first to a row and then to the product of rows.
`measurePreserving_firstBlockRectangleReversal` states the same result with
the literal submatrix function.

`HasRectangleReversalInvariance` is a Prop-valued predicate asserting this
preservation for every natural pair `a,b`.
`hasRectangleReversalInvariance` proves it. Both dimensions may be zero; no
positive-dimension assumption or determinant/Jacobian calculation is needed.
The only finiteness premise is the explicitly supplied sigma-finiteness of
the scalar Haar measure, already available for the p-adic consumer.

For any real normed target space, `integral_firstBlockRectangleReversal`
gives equality of the two total Bochner integrals for any function. This
identity alone asserts no convergence. The separate
`integrable_firstBlockRectangleReversal_iff` transports actual integrability
in both directions for any normed additive target group. Both follow from
the same measure-preserving measurable equivalence. In particular, the
integral theorem also applies to the pointwise norm as a real function.
The scalar and target universes are independent. This helper establishes
no quotient disintegration, lower-kernel identification or Laurent identity.
