# Split-torus rank comparisons

This is an internal derived unit for the split-rank part of the quaternionic
spin-group argument. It compares the actual split ranks defined by closed split
subtori, over an arbitrary field and without a characteristic restriction.

A finite map from a split torus on `I` to one on `J` induces a character pullback
with finite cokernel. The published finite-index rationalization theorem makes
this pullback surjective after tensoring with the rationals. The published
coordinate equivalences identify the resulting rational spaces with `J → ℚ`
and `I → ℚ`; the dimension inequality gives `Nat.card I ≤ Nat.card J`.
For an epimorphism on underlying schemes, injectivity of the integral character
pullback gives the reverse cardinal inequality directly over the integers.

Choosing splittings and composing the map with their isomorphisms gives the two
intrinsic split-rank inequalities. The input character-map results are from
`SplitTorusIsogenyCharacters`; the rank formulas and isomorphism invariance are
from `SplitRankReduction` and `SplitRankTransport`. These are derived consequences
of those Library results, with no additional external mathematical input.
