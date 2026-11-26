# Rank-one factors for pullback of an arbitrary character by the norm

`PadicCharacterNormFactorsStatement` takes a finite abelian Galois extension
of supplied p-adic fields in two independent universes. It uses the supplied
topological data, relative module topology, residue degree `f` and different
exponent. For any continuous quasicharacter of the lower field, the product
of the Tate Euler denominators over its norm-trivial twists is the Tate
denominator of its norm pullback evaluated at `X^f`. For unitary nontrivial
additive characters related by trace, the sum of the integer Tate epsilon
exponents is `f` times the upper exponent.

For the Euler calculation, first suppose the norm pullback is ramified.
Every lower character in the product has that same norm pullback. An
unramified lower character has unramified norm pullback by the normalized
order formula, so every lower factor and the upper factor is `1` in this
case. When the norm pullback is unramified, take an `f`th root of its
uniformizer value to construct one unramified lower lift of that character.
The ratio of the original lower character to this lift is norm-trivial.
Multiplication by that ratio permutes the twist set, and
`prod_lPolynomial_unramifiedNormTwists` calculates the resulting product.

For the exponent, `padicNormPullbackConductor` sums the multiplicative
conductors of the twists. The normalized trace formula multiplies the upper
additive conductor by `f`. Subtracting the two formulas yields the asserted
equality using the published Tate convention `epsilonExponent`.

The exponent is the spectral-variable part of Arthur–Clozel, Chapter 1,
equation (6.7), printed p. 60 (PDF p. 74), literature ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The Euler calculation extends the Library's unramified comparison by the
norm-character permutation.
