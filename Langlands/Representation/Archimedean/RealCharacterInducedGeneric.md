# Character-induced swaps with two generic factors

For a real character `c` and a complex character datum `d`, put
`ell = |d.weight|`, `a = d.exponent + ell/2`, `b = d.exponent - ell/2`, and
`s = c.exponent`. The theorem `RealCharacterInducedGeneric.injective_of_generic`
constructs an injective exact intertwiner from the actual `O(3)`-finite standard-module
function space for `[character c, induced d]` to that for `[induced d, character c]`.
Its hypotheses say that `s-a` and `s-b` avoid the two rank-one exceptional sets
`±(epsilon+2m+1)`, with the parity of the corresponding pair of position characters.
There is no real-part restriction on these two generic parameters.

The construction composes the block Frobenius maps `B0` and `B1` from
`RealCharacterInducedSwap`, using the generic multiplier of `RealBlockMultiplierGeneric`
for each. Nonvanishing of both multipliers gives injectivity of both maps. Their
recurrences give exact compact and Lie equivariance. The two recurrence parameters
differ by `ell`, so the proved character-first landing theorem, obtained from
`RealSwapLandingIntegral.inducedFirst` and its proved mirror, shows that the composite
satisfies the Fourier vanishing conditions of the target mixed standard module.
Corestricting the composite to that module preserves its injectivity and exact
equivariance. Exact intertwining modulo the bottom subspace is converted to
`IsRealStandardIntertwiner` by composition with the target identity map.

`genericMap` chooses the map constructed by that theorem; `genericMap_injective`
and `genericMap_isIntertwiner` expose its two properties.

This is internal derived content from the imported Frobenius, multiplier and landing
results. The proof follows the forward composite in Worker 763's character-induced
construction, replacing its tail multiplier by a nonvanishing generic multiplier.
The theorem retains its two generic-parameter premises and does not itself assert the
full unlinked swap.
