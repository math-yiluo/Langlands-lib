# Rank-one laws over an arbitrary affine base

This derived module proves the exact existing
`LocalSplitCell.RankOneLaws` for a supplied Weyl-normalized actual
opposite pair over an arbitrary commutative ring. Its hypotheses are
reductivity, a closed coordinate split torus maximal on every fibre,
a full fibrewise root datum, actual parametrizations at a root and
its negative, and the all-test Weyl action by that root's integral
reflection. No locality, reducedness, nonzero-ring or freeness
condition is added.

`LocalSplitCell.rankOneLaws_of_weylNormalization_affine` proves all
four identities on every scheme test: both conjugations by the
supplied three-factor Weyl point, its square as the actual coroot at
minus one, and the Gauss relation whenever the denominator `1 + x*y`
is a unit. The root maps and coroot are exactly the supplied original
maps and lattice vector. `RankOneLaws.rankOneNormal` projects these
laws to the existing `RankOneNormal` predicate, including its
original-base square equality.

The proof uses the actual rank-one centralizer and pointwise affine
étale unit-cell charts constructed in
`AffineOppositeRootNormalization`. A nonzero ring has a residue
field, which forces the integral coordinate pairing to be the
standard dot product. An isolating cocharacter gives the actual
coroot cell and the prescribed reflection on every chart. The
supplied Weyl action lifts to the centralizer and pulls back to
each coefficient ring. Centralizer rigidity and the published
unscaled-Weyl uniqueness calculation then force the chart's beta
coordinate to equal one.

`AffineRootNormalization.suppliedAffineEtaleWeylData` packages those
actual chart Weyl data together with their beta-one identity. The
ring-calculus theorem for beta-one Weyl data supplies all four laws
in exactly the supplied root and coroot coordinates.

`RankOneLaws.of_pointwise_etale_baseChange` descends these laws
without requiring any single chart to cover the base. The
neighborhoods through every base point form an actual fppf cover.
Its pullback to each test scheme detects equality of point
morphisms by the representable-sheaf separatedness theorem.
Naturality of the constant Weyl point, root evaluations and
cocharacter points, and the coordinate-preserving base-change
equivalences identify the pulled-back formulas with the chart
formulas. The denominator unit and its inverse restrict along
the test projection, preserving the exact relation.

The resulting centralizer laws compose with its actual inclusion
to give the laws in the ambient group. For the zero ring, every
scheme test has empty underlying space, so the required point
morphisms agree by initiality.

The provenance is composition and arbitrary-base generalization
of the imported actual chart, Weyl uniqueness and supplied-coordinate
ring-calculus results with fppf detection of morphism equality. This
does not assume a global ambient isogeny or any commutator-transfer
result, and it does not prove the whole affine split isogeny theorem.
