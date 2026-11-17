# Opposite-root normalization over an arbitrary affine base

This derived module constructs a unit rescaling of any supplied actual
opposite root pair over an arbitrary commutative ring. The ambient group
is reductive, its supplied coordinate split torus is a closed subgroup
and fibrewise maximal, and a full fibrewise root datum is supplied.
There is no locality, reducedness or nontriviality assumption on the ring.

`LocalSplitCell.normalizedAffineOppositePair` retains one unit of the
original ring and the all-test Weyl identity for the product formed from
the original positive root parametrization and the negative root
parametrization rescaled by this unit. Its torus action is exactly the
integral reflection of the supplied root datum.

The proof first handles the zero ring by the initiality of every test
scheme over its empty spectrum. For a nonzero ring, a residue field
forces the integral coordinate pairing to be the standard dot product.
An isolating cocharacter reduces the root pair to its actual rank-one
centralizer. The existing arbitrary-ring opposite-cell construction,
with the actual coroot, supplies the open triple cell.

At every prime of the base, the published field-reflection construction
gives a normalizer and unit cell coordinates on the residue fibre.
The pointed étale normalizer lift and an affine open shrinking retain
that residue point and extend both coordinates as units. The constructed
`AffineRootNormalization.affineEtaleWeylData` retains the actual
coefficient-ring normalizer, the same base-changed root maps and cell,
and its prescribed reflection. The integral pairing identifies the
ring-calculus reflection with the exponent reflection over every such
coefficient ring.

`AffineRootNormalization.etaleRankOneChart` packages these actual data
as charts through each prime. The imported pointwise normalization
theorem extracts a scalar from one original dual-number factorization.
Its image on each chart is the inverse beta coordinate, so the scalar
is a unit globally. Its inverse gives the required original-ring unit,
and pointwise étale equality detection descends the normalizer identity.
Finally composition with the rank-one centralizer inclusion gives the
Weyl identity in the original ambient group.

The provenance is a generalization of the imported local normalization
wrappers using the already published arbitrary-ring cell, field
reflection, pointed normalizer and affine coordinate constructions,
together with the supplied pointwise scalar-descent module. The
implemented proof does not assume that the base is local or that one
neighborhood covers the whole base. Initial global root parametrizations
remain inputs; construction of a whole normalized root family from
free root spaces is a subsequent application.
