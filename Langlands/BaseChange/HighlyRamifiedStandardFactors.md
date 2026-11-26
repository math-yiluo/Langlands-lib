# Standard factors after a sufficiently ramified determinant twist

`HighlyRamifiedStandardFactorsStatement` fixes a p-adic field, a nontrivial
unitary additive character `ψ` and a generic representation of `GL_(r+1)`.
There is a conductor bound such that every quasicharacter `χ` at or above
the bound gives the following comparisons for the JPSS standard pair,
with the trivial character of `GL_1` as its second member and a self-dual
measure for `ψ`. Every certified Euler polynomial is `1`. The integer
exponent of every certified epsilon factor is `(r+1)(a(χ)+n(ψ))`, where
`a(χ)` and `n(ψ)` are the multiplicative and additive conductors used in
Tate's rank-one exponent.

The proof chooses a nonzero principal-congruence fixed vector by smoothness.
It writes `ψ` as a scaling of a character of conductor zero and keeps the
same generic representation by independence of genericity from the character.
`UniformRankOneTwist.uniformRankOneTwist` supplies the bound and gives the
polynomial and exponent at conductor zero. Character change and uniqueness
of the polynomial give the polynomial at `ψ`. The epsilon exponent formula
for character change adds `(r+1)n(ψ)` to the conductor-zero exponent.

The starting local calculation is the standard pair case of Jacquet–Shalika,
*A Lemma on Highly Ramified ε-Factors*, Proposition (2.2), printed p. 320
(PDF p. 2), literature ID `jacquet-shalika-1985-ramified-factors`, SHA-256
`0864a6633c3cf430f576f91eadd05a7f11d88eea1b47095943d3ea76f7c9946b`.
The implemented proof uses the Library's level-uniform derivation and its
arbitrary-character JPSS normalization.
