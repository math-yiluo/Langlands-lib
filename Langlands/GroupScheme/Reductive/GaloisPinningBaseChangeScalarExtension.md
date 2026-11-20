# Canonical scalar-extension data for a Galois pinning

`GaloisPinningData.baseChangeScalarExtension` packages the canonical
base-change pinning in the existing `ScalarExtension` interface. It uses
the base-changed original torus and the canonical group and torus tower
isomorphisms. The root-datum equivalence preserves the base and
intertwines the full relative star action. Its map on characters is the
existing `weightTransport`.

The inclusion square follows from naturality of the group tower
isomorphism, with the torus isomorphism as its commutative version. This
internal construction allows comparisons expressed in the
`ScalarExtension` interface to use the canonical base-change pinning.
