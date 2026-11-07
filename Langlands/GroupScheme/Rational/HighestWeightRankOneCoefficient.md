# Rank-one nonvanishing from actual highest-weight data

This internal derived unit uses a supplied split pinning with full coroot span,
an actual highest-weight representation, two supplied additive maps with opposite
torus characters, and their supplied all-relative-test root-cell relation. It
asserts no existence of these data.

`HasHighestWeightRankOnePairing` is the proposition that every nonzero vector
of the original highest-character space admits a normalized functional giving
all of the stated binomial pairings for the two supplied additive maps.
`hasHighestWeightRankOnePairing` proves this condition from the supplied data.

The actual character-space equation, evaluated along the supplied cocharacter,
gives its lattice-pairing power on every highest vector over the base field.
When this integer pairing is a natural number, this is exactly the coroot-weight
premise in the original rank-one coefficient calculation.

For any nonzero original highest vector, a separating dual functional is
normalized to take value one and composed with the actual highest-character
projector. The projector fixes the vector and kills every positive-degree
lowering coefficient on the whole representation. The scalar polynomial
recovery lemma therefore gives lowering invariance of the composed functional.
The raising action fixes the vector on every relative scheme test, and in
particular at every base-field scalar parameter.

These derived fixed-data properties and the supplied root-cell relation give
all diagonal and off-diagonal binomial pairings of the original raising and
lowering divided powers over an infinite field. Nonzero binomial coefficients
force nonzero lowering on every supplied nonzero highest vector. In prime
characteristic, the published Steinberg binomial identity gives nonvanishing
of every retained lowering coefficient when the coroot pairing is `p^r - 1`.

The provenance is the existing actual character-space/cocharacter evaluation,
highest-weight projector, coefficient-shift and fixed-vector results, the
rank-one cell coefficient calculation, and the proved binomial identity.
No external source is invoked. This is a single-root conclusion; simultaneous
full-unipotent top-action nonvanishing, an entire induced-space dimension bound,
and structural or highest-weight existence remain separate obligations.
