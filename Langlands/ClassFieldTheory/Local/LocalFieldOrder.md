# Normalized order on the units of a local field

Serre, *Local Fields*, Chapter XIII, §3, Propositions 6 and 7, uses the
integer-valued valuation that takes a uniformizer to one. This module gives
that normalization for the local fields in Mathlib. It supports the
valuation map in Proposition 6 and the extension formula in Proposition 7.

The module transports the intrinsic multiplicative valuation to the
multiplicative copy of the integers with zero. On the actual field units,
the negative logarithm gives an additive homomorphism to the integers.
The minus sign gives positive order to elements of the maximal ideal.
The order is surjective because the intrinsic valuation attains every value.

For a valuative extension of local fields, the upper order of a base
uniformizer is positive. This integer gives the ramification factor.
Subtracting the order of a field unit times the uniformizer in additive
notation leaves an element of order zero. The value-group map preserves
this condition, which proves that the upper order is the lower order times
the ramification factor. This argument applies without a separability or
characteristic hypothesis.

The underlying multiplicative valuation is `Langlands.FML.normalizedMultiplicativeValuation`. [Normalized multiplicative valuation](../../LocalFactor/FML/Valuation.md)
