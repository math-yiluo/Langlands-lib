# Natural bilinear pairings of units

Worker 794.

This internal supporting development treats natural separately multiplicative
pairings of two global units with values in a commutative group scheme.
It is intended for the diagonal-commutator argument in the central-extension
splitting theorem.

`UnitPairing Z` supplies such a pairing on every test scheme, together with its
compatibility under every restriction of tests. No separatedness assumption
is needed for this data or the finite-order vanishing results.

The finite-order result uses an fppf refinement adjoining a root of the second
input. Separate multiplicativity moves the exponent to the first input, where
the finite-order assumption makes it the identity. Equality descends from the
fppf refinement and then from an affine cover for arbitrary tests.

If `Z` is separated over the base, `UnitPairing.eq_one` applies
`units_natural_ext` to the first input with the second fixed under restriction.
The finite-order result supplies the root-of-unity premise. Consequently every
such natural pairing is identically the identity point, without restrictions
on the base or test schemes.
