# Adic Hom effectivity across nilpotent base reduction

A surjective map from a local ring with nilpotent kernel
induces an isomorphism on the first quotient by the maximal ideal,
using the image of that ideal in the target. This is
`isIso_quotientSpecMap_zero_of_surjective`. The construction
`firstQuotientIsoOfNilpotentSurjection` packages it in the slice over
the original affine base.

For a compatible adic homomorphism system from a group of
multiplicative type to a smooth group, suppose an actual
homomorphism over the quotient agrees with the first quotient
of the pulled-back system. The published square-zero cohomology
and nilpotent induction lift that actual homomorphism.
The actual first-quotient isomorphism detects equality of its
first restriction with the original system. This establishes
`HasFirstQuotientLift` before nilpotent base reduction.

The internal argument combines the existing infinitesimal lifting
and extended-ideal pullback comparison. On a Noetherian ring
it applies in particular to the quotient by the nilradical, and
the first-quotient effectivity theorem recovers the higher
thickenings over the complete base.
