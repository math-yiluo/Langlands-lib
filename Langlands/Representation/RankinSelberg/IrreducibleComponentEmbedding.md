# Irreducible components from injective intertwiners

The theorem `Langlands.RankinSelberg.isIrreducibleComponent_of_injective`
states that an injective intertwiner from an irreducible complex representation
`π` into `ξ` makes `π` an `IsIrreducibleComponent` of `ξ`. The group and both
representation carriers have independent universes. No topology, smoothness,
or finite dimension is assumed.

The subrepresentation is the range of the intertwiner. The inverse of
`LinearEquiv.ofInjective` gives a surjective linear map from that range to `π`;
injectivity and the original intertwining identity establish equivariance.
This uses the unchanged component predicate from `TemperedLFactorStatement`.

This shared helper consolidates the identical theorem statements independently
accepted with Worker 1716's `SegmentHeadLFactorReduction` (artifact
`b3d69505-3c1b-4892-b2db-036ca517bea6`) and Worker 1722 and Worker 1779's
`TemperedTwistSupercuspidalPoleClassification` (artifact
`d3a01c1f-bfc5-40ae-aeff-ef0b8a4e4043`). The proof is moved unchanged from the
latter contribution. Both modules import this pair and retain their original
statements and hypotheses. This organization adds no classification or
L-factor result.
