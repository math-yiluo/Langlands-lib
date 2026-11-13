# Rectangular matrix coordinates for rank-one Hermitian spaces

This internal supporting module constructs genuine coordinates between different
finite source and target index types and applies them to a supplied nondegenerate
Hermitian space with attained maximal totally isotropic dimension one. The
quadratic extension, pairing and actual isotropic-submodule hypotheses are inputs.

The coordinate matrix has target rows and source columns. The matrix of the
inverse equivalence gives a reverse rectangular matrix; their two products are
the corresponding identity matrices, by the composition rule for
`LinearMap.toMatrix'`. Expanding entries against two standard coordinate vectors
turns equality of the full pairings into the Gram congruence
`(P.map c.bar).transpose * B * P = J`. This argument works over any commutative
ring and does not require the source and target index types to be definitionally
equal.

For the Hermitian application the coefficient fields share an arbitrary universe,
and the vector-space or source-index universe is independent. An actual totally
isotropic submodule whose dimension in `ENat` equals one contains a nonzero
vector. The maximality bound, also in `ENat`, becomes the natural-number bound
required by `exists_rankOne_gram_coordinates`. That theorem supplies a hyperbolic
plane and the negative anisotropic diagonal middle. The existing
`DiagonalForm.exists_unitWitnesses` supplies units for every middle weight.

For a finite source of cardinality `n + 1`, with `n ≥ 1`, its function space has
dimension `(n - 1) + 2`. Applying the construction gives exactly
`Index (Fin (n - 1))` coordinates, both inverse matrix identities and the full
Gram congruence. In particular the source may be `Fin (n + 1)`, without silently
identifying it with the sum type used by the Hermitian model.

The provenance is elementary internal linear algebra: the imported actual
hyperbolic splitting and anisotropic diagonalization, unit witnesses, Mathlib's
linear-map-to-matrix composition formula, and a finite-sum calculation on standard
coordinate vectors. No characteristic restriction or division by two is used.
This module does not establish the split-rank/Witt-index comparison, construct
a Hermitian presentation from a Tits index, or give a group-scheme isomorphism.
