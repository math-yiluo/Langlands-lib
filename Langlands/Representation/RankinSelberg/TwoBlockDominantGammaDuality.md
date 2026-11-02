# Unequal-rank gamma reflection for the dominant-rank argument

This is an internal deduction from the published actual dual-model maps and
fixed-functional gamma equations. It does not assume Whittaker type or prove
either final dominant-rank multiplicativity statement.

The block Weyl representative is the permutation of the involutive tail
reversal. It is fixed by inverse transpose and has square one. Consequently
applying twice the first dual transform followed by this block translation
recovers the original raw function. The second dual transform also has square
one. Equality of raw functions identifies the actual iterated unequal-rank
integrals even when their character covariance certificates differ.

The second dual model map is surjective. Transporting the original minus-one
scalar along this map gives the same scalar on the dual model: inverse
transpose commutes with matrix negation. The scalar is unique for a nonzero
second functional and has square one.

For a residue cardinality greater than one, the fixed gamma equation is
equivalent to its reflected rational-function identity. An original equation
and a dual equation with the original and dual continuations interchanged
therefore imply that the product of the original gamma factor and the
reflected dual gamma factor is one, provided the original continuation is
nonzero. The proof reflects the dual identity, substitutes the original one,
uses the square-one scalar, and cancels the nonzero continuation.

`unequalRankGammaEquation_reflection_mul` supplies these data from two actual
`UnequalRankGammaEquation` certificates. It chooses a nonzero original value
at the complementary rectangle with first block zero, applies the original
equation to its realizing model vectors, and applies the dual equation to
their actual translated first and second dual model images at the exchanged
rectangle. Uniqueness of rational continuation identifies both pairs of
continuations, using the double-dual integral identity. The additive and
quotient measures are unchanged throughout. No Fourier transform or
self-duality hypothesis is needed in this strictly unequal-rank lemma.

`UnequalRankGammaDualReflectionLaw` packages this implication for every two
rational factors on the specified models. `unequalRankGammaDualReflectionLaw`
proves it when the second functional is nonzero, the cardinality is greater
than one, and the complex unit defining rational reflection is its reciprocal.
There is no existence claim for a gamma factor in this packaged implication.
