# Positive integral root cones and additive depths

This internal construction uses the actual character lattice, actual relative
roots, and integral character–cocharacter pairing of the supplied torus inclusion.

`positiveIntegralRootCone i a b` consists exactly of the actual roots of the
form `p*a + q*b` with positive natural `p,q`. Neither input is inserted unless
it already has such a representation. A cocharacter positive on both inputs
is positive on this entire cone. Positive integral combinations of cone roots
remain in the cone whenever they are actual roots.

Every additive real depth function satisfies the closed-positive collection
condition on this cone. The combination inequality is an equality, and
`f(2*c) = 2*f(c)` gives the required double-root absorption bound. The closure
of the union of these actual cone filtrations is exactly the V3 generated
subgroup with depths `p*f(a) + q*f(b)`. The proof compares the literal unions
in both directions, retaining all representations and all doubled roots.

For two characters independent in the rationalized character lattice, any two
real numbers extend to an additive depth function. The proof defines a linear
map on the span basis of those two rational vectors, extends it to the full
rational vector space, and composes with the original lattice map.

Separately, local opposite factor pairs for a smooth affine group and a
monomorphic split torus inclusion imply that every positive actual root is
an indivisible positive root or its double. The proof uses the existing
integral ray descent and the existing classification of actual roots with
a common positive integral multiple. Indivisibility excludes the remaining
case where the indivisible root is twice the original root. Consequently any
complete enumeration of indivisible positive roots covers every selected
positive root by an entry or its double. This needs no apartment or
relative-root-system realization.

The internal provenance is the published actual root-ray and opposite-factor
pair results, elementary additive-lattice calculations, and linear-map extension
from a subspace. These results provide cone and cover ingredients; they do not
yet prove V3 under field restriction, handle dependent input depths, construct
a valuation or apartment, or establish the supplied-model building comparison.
