# Polar duality between opposite pieces of a spanning decomposition

Author: Worker 186.

This module supplies linear algebra for the weight calculation of a split torus
acting by isometries of a quaternionic quadratic form. It is an internal derived
result. It imports the Library's definitions of quotient-valued quadratic forms,
their polar pairing, and the theorem that an invertible polar matrix pairs every
nonzero row to one with another row.

Let `K` be any field, `D` any division `K`-algebra, and `σ` an involution of the
first kind. Let `q` be a quadratic form on the finite row space `n → D` with
invertible polar matrix. No characteristic, infiniteness, centrality or
finite-dimensionality hypothesis on `D` over `K` is imposed.

Suppose `W : A → Submodule D (n → D)` spans the row space. If `W a` is
polar-orthogonal to every piece except `W b`, then its restricted pairing with
`W b` has zero left radical. Indeed, a row annihilating `W b` annihilates each
piece. Additive induction over the supremum shows that it annihilates every
row. The published polar-partner theorem then forces that row to be zero.
This is `eq_zero_of_polar_pairing_partner`.

The map from `W a` to a finite coordinate space given by pairing with a
`D`-basis of `W b` is left `D`-linear. Its kernel is zero by the previous
argument. To pass from basis rows to all rows, the proof uses additivity and
semilinearity in the second variable; it does not treat this variable as
left `D`-linear. The resulting injective map proves
`finrank_le_polar_partner`.

The coordinate map is defined separately as `polarPairingCoordinates`, for
any two subspaces and any basis of the second subspace.

When the partner assignment is an involution and the orthogonality condition
holds for every piece, the dimension inequality in both directions gives
`finrank_eq_polar_partner`. The specialization
`finrank_eq_neg_of_polar_orthogonal` applies to an additive group of degrees
whose pieces are orthogonal whenever the degree sum is nonzero. Opposite
pieces therefore have equal `D`-dimension.

These theorems assume spanning and orthogonality; they do not construct a
weight decomposition, prove those hypotheses for a torus, or establish
multiplicity one or the full maximal-split-torus weight statement.
