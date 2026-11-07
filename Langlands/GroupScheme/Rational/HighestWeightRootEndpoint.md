# Actual root-string endpoints and rational Weyl images

This derived unit uses an affine group scheme over a field, a supplied split
pinning, and a finite matrix representation. For an actual root `i`, an
additive map equivariant by minus that root, and a natural number `m` equal to
the pairing of the character `lam` with `coroot i`, `rootEndpointMap` restricts
the actual degree-`m` lowering coefficient to the character space of `lam`.
Its codomain is the character space of the reflected character. This construction
alone asserts no highest-weight condition or nonvanishing.

The root datum supplies actual rational normalizers for every root reflection.
Their invertible matrices give equal dimensions for a character space and its
reflection.

The endpoint conclusions additionally assume an infinite field, finite root
index, full integral coroot span, and the original `IsHighestWeight` condition
at `lam`. The chosen root must be strictly positive on the polarization of the
integral Weyl vector. Supply opposite equivariant additive maps and their linked
coroot relation over every relative test scheme. The normalized binomial pairing
at degree `m` has value `choose(m,m)=1`, so the endpoint coefficient is nonzero
on every nonzero highest vector. Thus `rootEndpointMap` is injective; equality
of the character-space dimensions makes it bijective.

For every actual rational normalizing point whose character action is the chosen
reflection, and every nonzero vector in the highest-character space, the endpoint
is a unit scalar times that point's matrix image of the vector. Both vectors
belong to the reflected highest-character space, which has dimension one.
Neither vector is zero, so the scalar relating them is nonzero.

The final existence theorem retains these highest-weight, infinite-field, full
coroot-span, positivity and natural-pairing hypotheses. It derives the linked
maps and their all-test relation from the supplied pinning; it needs no extra
root-cell premise. Its endpoint equation quantifies over every such rational
reflection representative and every nonzero highest vector.

The provenance is the imported signed coefficient shifts, actual normalizer
equivalence, highest-weight binomial pairings, and arbitrary-rank linked
root-cell construction. No external source is used. These are single-root
endpoint conclusions; an ordered full-unipotent top-action formula and the
entire induced-space dimension bound remain separate obligations.
