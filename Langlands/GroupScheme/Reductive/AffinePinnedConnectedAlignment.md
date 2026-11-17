# One based coordinate alignment over a connected base

This internal helper concerns supplied comparisons of affine pinned models on
a common preconnected scheme with a specified point. The comparison is assumed
to preserve the canonical Borel, and its supplied actual coordinate-torus
isomorphism is assumed to satisfy the inclusion square.

The residue-field comparison at the specified point supplies a full based
root-datum equivalence and its formula on the entire character lattice, using
`exists_fieldCoordinateData`. The constant homomorphism family attached to the
original torus map acts by the corresponding exponent matrix on that fibre.
The open-and-closed exponent locus and preconnectedness extend this action
over the whole base. The full character formula then follows from the linear
weight-map matrix formula. This produces a `BasedCoordinateIso` whose actual
ambient and torus maps are exactly the supplied maps.

For a connected common scheme a point can be chosen from nonemptiness. This
result chooses a single full based root-datum equivalence; it does not construct
a pinned representative or prove preservation of the chosen pinning vectors.
