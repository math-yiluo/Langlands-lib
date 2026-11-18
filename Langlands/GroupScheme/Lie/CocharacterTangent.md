# Actual tangent vectors of cocharacters

Over any field `k`, `gmInfinitesimal a` is the actual dual-number tangent
point of the multiplicative group whose unit value is `1 + a ε`.
`cocharacterTangent y` is its image for `a = 1` under the actual
cocharacter `y : Gm → T` of a commutative group scheme `T`.

For a character `chi` of `T`, `characterValue_cocharacterTangent` states
that the character value at this tangent point is the infinitesimal unit
with coefficient equal to the integer pairing `latticePairing T chi y`,
cast into `k`. The `snd` corollary gives that coefficient directly.

`cocharacterTangent_comp` records naturality under a homomorphism of
commutative group schemes. For a split torus in characteristic zero,
`cocharacterTangent_injective` shows that the actual tangent point
determines the integral cocharacter: evaluate all characters, use
injectivity of the integer cast into `k`, and then use that characters
separate homomorphisms into a split torus.

For every split torus, in arbitrary characteristic,
`span_cocharacterTangent` states that the additive versions of its
cocharacter tangent vectors span its actual Lie kernel over `k`. For a
standard split torus, `cocharacterTangent_single` identifies a coordinate
cocharacter with the corresponding coordinate infinitesimal vector.
`span_cocharacterTangent_standard` then writes every tangent vector as a
linear combination of those vectors using
`splitTorus.infinitesimalLinearEquiv`. The general proof transports this
span through a splitting isomorphism and uses
`cocharacterTangent_comp` to retain actual cocharacters of the given
torus. This span theorem is valid in positive characteristic as well;
it does not assert injectivity of the integral cocharacter map there.

The evaluation proof rewrites the composite `y` followed by `chi` as the power map
with exponent given by `gmEndEquiv`, then uses the published integral-power
formula for `splitTorus.infinitesimalUnit`. This is an internal derived
construction and linear-algebra helper for the cocharacter action in Task 7128's Lie-weight input to
Freudenthal's formula. The basic construction and evaluation make no character-formula,
characteristic-zero, splitness or reductivity assumption. The further
injectivity and span theorems have the hypotheses stated above.
