# The finite divisor of an actual idele

For a number field `E : Type u`, this module constructs the finite divisor map
on Mathlib's actual `IdeleGroup (𝓞 E) E`. It uses the finite places
`HeightOneSpectrum (𝓞 E)` and their published completion coordinate maps. No
Galois extension or action is needed for this construction.

`FinitePlaceDivisor E` is the additive group of finitely supported functions
from finite places to the integers. For an idele `x`, its coefficient at `w` is

`ideleOrder w x = -Multiplicative.toAdd (unitsExponent w (ideleCoordinate w x))`.

The negative sign is essential: `unitsExponent` is the exponent of Mathlib's
multiplicative valuation and takes the value `-1` on a uniformizer. Thus this
coefficient uses the usual divisor order, positive on a uniformizer. The module
reuses that local exponent and the actual coordinate map, rather than choosing
local generators or a replacement idele group.

`ideleOrder_one` and `ideleOrder_mul` give the order laws. The theorem
`ideleOrder_eq_zero_iff` identifies order zero with valuation one at the chosen
finite place. The finite-support theorem projects an idele to a unit of the
finite adele ring and applies Mathlib's
`FiniteAdeleRing.hasFiniteMulSupport_valued`. Its support contains every place
where the new order is nonzero, by the order-zero criterion.

`ideleDivisor` packages these coefficients as a finitely supported function;
`ideleDivisor_apply` gives its coefficient formula. The identities
`ideleDivisor_one` and `ideleDivisor_mul` package it as the homomorphism

`ideleDivisorHom E : IdeleGroup (𝓞 E) E →* Multiplicative (FinitePlaceDivisor E)`.

The multiplicative tag changes notation only: multiplication in the codomain
is addition of divisors. `ideleDivisor_eq_zero_iff` proves that the kernel
consists exactly of the ideles whose coordinates have valuation one at every
finite place. The infinite coordinates are unrestricted.

The formula `ideleDivisor_ofAdicCompletion` computes the divisor of the idele
with a single nonidentity local component: it is the single divisor at that
place with coefficient the negative of its local valuation exponent.
`exists_ideleDivisor_single` applies the published local exponent surjectivity
to realize any integer coefficient. Finally `ideleDivisor_surjective` uses
finitely supported function induction: the zero divisor comes from the identity
idele, and a sum of a single divisor with a previously realized divisor comes
from the product of their two preimages.

The source is J. S. Milne, *Class Field Theory*, v4.03 (2020), Chapter V §4.1,
printed page 170 (PDF page 179). There the canonical map sends an idele to the
product of finite prime ideals raised to its local orders; it is surjective and
has kernel `I_{S∞}`. The paragraph immediately following §4.1 identifies the
quotient with a direct sum of copies of the integers. The single local
embedding used here is the one described in §4.3 on printed page 171 (PDF page
180). This module is a derived finite-divisor presentation of that construction:
it implements the orders, finite support, kernel criterion and surjectivity.
Identification of finite divisors with nonzero fractional ideals, descent to
the ideal class group, equivariance and any cohomological conclusions are
separate obligations and are not asserted here.

The registered source is `milne-2020-class-field-theory`, with SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
