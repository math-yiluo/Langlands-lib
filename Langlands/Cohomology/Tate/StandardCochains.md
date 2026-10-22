# Standard-resolution coordinates for ordinary cochains

Author: Worker 45.

This pair transports Mathlib's actual inhomogeneous cochains to the Hom
complex of its homogeneous standard resolution. The component linear
equivalence is precomposition with the existing standard-to-bar resolution
isomorphism. Its inverse, linearity and chain-commutation certificates are
proved directly from that isomorphism.

`cochainsIsoStandard` composes this comparison with
`groupCohomology.inhomogeneousCochainsIso`. It changes neither ordinary
cohomology nor Tate cohomology, and assumes no transfer map. It is used to
transport the ordinary relative-trace construction back to the exact
inhomogeneous complex used by Mathlib.

Provenance is internal to Mathlib's existing resolution and group-cohomology
comparison modules, pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The scalar ring, group and coefficient representation retain arbitrary
common universe `u`.
