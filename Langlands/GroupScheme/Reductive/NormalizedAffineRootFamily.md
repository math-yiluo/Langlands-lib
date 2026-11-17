# Weyl-normalized root families over arbitrary affine bases

This derived construction gives actual parametrizations of every root,
with all simple opposite pairs simultaneously Weyl-normalized, over an
arbitrary commutative ring. Its hypotheses are reductivity, a closed
coordinate split torus maximal on every fibre, a full fibrewise root
datum, a base of that datum, and free actual root weight spaces. These
are the corresponding hypotheses of the affine split isogeny target.

`normalizedAffineRootFamily` first uses the published global
parametrizations from free root weights. The more general
`normalizedAffineRootFamilyOfMaps` starts with any supplied family of
actual root parametrizations. Its simple positive maps are preserved
exactly, as recorded by `normalizedAffineRootFamilyOfMaps_eq_simple`.

For each simple root the imported arbitrary-affine-base opposite-pair
normalization constructs a unit rescaling of its opposite map. Negative
simple roots are distinct, and none is simple positive, so these
rescalings can be inserted independently into the original family.
All other root maps are retained. Scaling by a unit preserves the
actual root-parametrization predicate. The chosen opposite pairs have
the exact all-test torus reflection required by `IsWeylPoint`.

The provenance is composition of the published free-root-weight global
parametrizations and the supplied arbitrary-affine opposite-root
normalization, followed by the finite simple-root replacement argument
used in the published local-family construction. No local-ring,
reduced-ring or nonzero-ring condition is added. This construction
supplies normalized families; commutator relations and their
compatibility across a root-datum isogeny remain separate obligations.
