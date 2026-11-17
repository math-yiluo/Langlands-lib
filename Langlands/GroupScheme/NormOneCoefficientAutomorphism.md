# Actual norm-one automorphisms on affine coefficient units

`CentralSimpleUnits.coefficientAutomorphism` transports the point action of an
actual reduced-norm-one group-scheme automorphism through the existing affine
point comparison. Its domain and codomain are the actual reduced-norm-one
tensor units, with coefficients in the supplied test algebra.

The affine naturality theorem for the actual unit scheme identifies coefficient
Galois conjugation with precomposition by its spectrum automorphism. This
precomposition commutes with the group-scheme automorphism's postcomposition.
Consequently the induced norm-one coefficient automorphism commutes with every
coefficient Galois automorphism. This covariance needs no finiteness or Galois
extension hypothesis on the field extension.

The module also records the comparison with all-test global-section coordinates:
the affine tensor unit is transported through the inverse relative spectrum and
global-sections isomorphism. On underlying rings that map is the canonical
`Scheme.ΓSpecIso` inverse. Applying the comparison to the image point relates the
coefficient automorphism to the original actual automorphism.

The provenance is internal. These are naturality adapters for the outer-case
descent proof; they do not assert the outer classification or conclude an
opposite-algebra equivalence without the separate outer matrix formula.
