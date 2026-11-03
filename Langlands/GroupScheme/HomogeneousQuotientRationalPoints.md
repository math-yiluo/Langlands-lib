# Actual rational lifts from sections and finite quotient fibers

Author: Worker 1436.

This internal adapter unit preserves identity-test rational points and the
supplied actual map. It constructs lifts when the indicated section or
finite-field torsor input is available.

Over a commutative local base ring, `rationalPointInOpen` factors an actual
identity-test point through an open containing the image of the base's closed
point. The existing `range_subset_open_iff_closedPoint` proves containment of
the whole spectrum image, and `openPointLift` constructs the factorization.
The identity-test and `RingPoint` conventions are transported through
`rationalPointEquiv`. The composite with the open immersion is proved equal
to the original point.

`rationalLiftThroughOpenSection` composes that factorization with a given
section. Its composite with the supplied map is the original point.
Consequently sections around every topological point imply rational lifts.
This step applies in particular over every field and does not assume a
topology on the base ring or any density of ambient rational points.

Over a finite field, `rational_lifts_of_finite_torsor_identity` transports
the existing actual-fiber torsor bridge to identity-test points, using the
naturality and injectivity of the same carrier equivalence.
`rational_lifts_pseudo_of_finite_torsor_and_connected` specializes it to a
pseudo-parabolic inclusion. Closedness makes the inclusion monic and the
subgroup affine. The isomorphism to the actual identity fiber, established
in `HomogeneousQuotientFiber`, gives subgroup smoothness from the supplied
quotient map. Connectedness of the subgroup and the full
`FiniteFieldTorsorPointStatement` are retained inputs.

These are conditional adapters. They prove neither the finite-field torsor
point proposition, the connectedness of a pseudo-parabolic subgroup, nor
the existence of local sections in the general infinite-field case.
Their provenance is internal: actual open-immersion factorization, point
carrier naturality, the existing actual quotient-fiber torsor, and the
identity-fiber isomorphism.
