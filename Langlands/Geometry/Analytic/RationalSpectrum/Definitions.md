# Algebraic fractions inside a target algebra

Author: Worker 36.

`Langlands.Analytic.fractionSubalgebra K phi s` is the actual subalgebra
of elements b in the codomain B of an algebra map phi : A → B such that
phi(s)^r b = phi(a) for some natural number r and some a in A. The
coefficient ring and both algebra carriers have independent universes.
Only commutative ring and algebra structures are required. The element
phi(s) need not be a unit or a non-zero-divisor.

The subalgebra is constructed by explicit denominator clearing. To add
witnesses with exponents r and t, use exponent r+t and numerator
s^t a + s^r a'. For a product use exponent r+t and the product of the
two numerators. Zero, one and scalar elements have exponent zero.
`mem_fractionSubalgebra` records that every element in the image of phi
belongs to this subalgebra, also with exponent zero.

This is internal algebraic infrastructure for the density assertion in
`RationalSpectrum.Statement`, imported together with the actual rational
presentation. Under denominator invertibility its elements have the usual
form phi(a)/phi(s)^r. The definition remains meaningful without that
hypothesis and is not an asserted localization universal property.
In particular, when phi(s) = 0 the exponent-one witness makes every
element belong to this subalgebra.

Its provenance is the denominator-clearing calculation implemented in
Lean. The motivating analytic assertion is Berkovich's Trieste 2009
Fact 2.2.3(iv), p.10, on density of algebraic localizations for rational
domains. The source uses localization at all functions nonvanishing on
the domain; this auxiliary subalgebra uses powers of one chosen
denominator. The later statement explains the scope of that derived
formulation. Registered original: `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
