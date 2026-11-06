# Actual relative fixed-exponent cocharacter centralizers

This internal module constructs the actual centralizer of a fixed integer-coordinate
cocharacter of a supplied standard split torus in an affine group scheme over an
arbitrary commutative ring. The original group may have disconnected fibres.
No reductivity hypothesis is used.

The group is the existing affine dynamic centralizer construction, with its
specified closed inclusion into the original group. It represents centralization
on every test scheme. The original torus factors through it, recovering the given
torus map after inclusion; that factor remains closed when the original map is
closed. The centralizer is affine, and is smooth whenever the ambient group is
smooth, over the arbitrary base ring.

Under any affine base change the cocharacter retains exactly its specified integer
coordinates. The pullback of the actual relative centralizer inclusion therefore
represents the centralizer of that same-coordinate cocharacter in the pulled-back
ambient group. This comparison is on every test scheme.

For a smooth ambient group, the map induced by inclusion on the actual geometric
identity components represents the centralizer of the corresponding cocharacter
inside the actual geometric identity component of the original group. The source
is the actual identity component of the actual geometric fibre of the constructed
relative centralizer. The target is the actual identity component of the original
geometric fibre at the same base point and with the same chosen residue-field
algebraic closure. The actual standard-torus maps into these two components commute
exactly with this inclusion.

Its actual roots are precisely the ambient actual roots whose integer dot
product with the cocharacter vector is zero. For every such character, the
weight-space dimension in the centralizer identity component equals the
ambient dimension. The proof identifies the canonical torus map with its
factor through the represented internal centralizer and uses the actual
centralizer Lie comparison.

The supporting field construction `Dynamic.centralizerWeightSpaceEquiv`
gives the full linear equivalence for every character annihilating a
cocharacter, for any affine locally finite type ambient field group and
any affine representative of its actual centralizer. It is induced by the
specified inclusion differential. Its surjectivity follows because the
ambient weight vectors lie in the actual centralizer tangent image.
Neither smoothness nor reductivity is assumed in this field comparison.
The weight-image equality is the existing
`RootReducedness.map_weightSpace_torusFactor` from
`Reductive.RootTangentRankOneReduction`; the present module reuses it to
construct the single-weight linear equivalence.

The provenance is internal. The construction combines the existing affine
dynamic centralizer and its factorization properties, arbitrary-ring centralizer
smoothness, the fixed-exponent cocharacter base-change formula, all-test base change
of represented centralizers, and the comparison identifying the identity component
of an ambient centralizer with the centralizer in the ambient identity component.
It introduces no new field classification claim and does not establish reductivity
or the final openness theorem.
