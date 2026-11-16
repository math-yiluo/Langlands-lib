# Scalar extension of supplied affine pinned models

This internal module constructs the full supplied `AffinePinnedModel` after
arbitrary extension of its coefficient ring. It uses the actual group
pullback, the canonical normalized coordinate inclusion, the original full
root datum and base, and scalar extension of the original pinning vectors.

The published arbitrary-ring exponent weight-space equivalence for smooth
affine groups identifies each tensor-extended original weight line with the
actual weight line in the scheme pullback. Tensoring the supplied line
trivialization and using the tensor right-unit identification gives the new
trivialization. Its value at one is exactly the actual scalar extension of the
original chosen vector.

The projection and point-identification formulas show that the new chosen
vector is exactly the `rootVectorPoint` previously used in the concrete
local-test pinning predicate.

Reductivity, closedness, fibrewise maximality and the full coordinate
root-datum condition use their published base-change laws. The test ring is
arbitrary, including nonreduced rings. This construction does not assert local
geometric existence or uniqueness of normalized comparisons.
