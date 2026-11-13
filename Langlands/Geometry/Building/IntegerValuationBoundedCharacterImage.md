# Finite character-valuation images of algebraically bounded sets

This internal derived unit works over an arbitrary field with an integer-valued
valuation compatible with its valuative relation. Algebraic boundedness is the
existing bound on every actual regular function; the character valuation is the
existing map on actual rational characters and rational points.

For a bounded set, the universal regular section of each rational character
bounds its multiplicative valuation above. Taking the integer logarithm gives
a lower bound for its source-positive character-valuation coordinate. Apply the
same argument to the negative character and use additivity in characters to
obtain an upper bound. Every coordinate therefore belongs to a finite integer
interval.

For a connected reductive group, the published `rationalCharacterLattice`
theorem supplies a finite basis of the actual rational character lattice.
Evaluating additive integer-valued maps on that basis is injective. The
character-valuation image embeds into the finite product of the coordinate
images, so the full image is finite.

Choose one element of the original set above each value in that finite image.
Equality of character valuations says that the quotient of two representatives
belongs to the kernel, which is the published `characterValuationKernel`.
Thus `exists_finite_characterKernel_representatives_of_isAlgebraicallyBounded`
provides a finite subset `T` of the bounded set such that every `g` in the set
has `t⁻¹ * g` in that actual kernel for some `t ∈ T`.

`BoundedCharacterValuationImageStatement` is the arbitrary-universe proposition
asserting full character-valuation image finiteness under the displayed
compatible-valuation and connected-reductive hypotheses. The accompanying
`boundedCharacterValuationImage` proves precisely that proposition.

These are algebraic statements about arbitrary bounded sets, with no subgroup,
topology, local compactness, or residue-field finiteness hypothesis. Their
provenance is the regular-function definition of boundedness, the published
universal-character evaluation identity, and finite generation of the published
character lattice. This is the character-image step of the bounded normalizer
argument in Kaletha--Prasad, Proposition 4.2.13, printed p.173 / PDF p.204,
registered source `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
No normalizer covering, building
metric, bounded orbit, or fixed-point assertion is proved here.
