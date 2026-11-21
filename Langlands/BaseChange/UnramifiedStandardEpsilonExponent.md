# Standard epsilon exponents under unramified twists

`UnramifiedStandardEpsilonExponentStatement` uses the carrier of a
`PadicField p` with its canonical local-field data. It starts with an actual
standard pair epsilon certificate against the trivial rank-one character.
A determinant twist by any character trivial on the valuation units gives
a certificate with the same exponent at the supplied additive character
and self-dual measure. Its unit coefficient may change.

An unramified character is determined by its nonzero value on a chosen
uniformizer. A spectral point realizes this value, so the character is a
complex power of the normalized absolute value. The published
`unramifiedTwistEpsilon` then gives a twisted certificate with the original
exponent, and the ordered pair is the standard pair with second rank one.

The Library's globalization specifies the original component up to an
unramified determinant twist. This specialization of `unramifiedTwistEpsilon`
removes that twist in the formal adaptation of Arthur–Clozel, Chapter 1,
proof of Proposition 6.9(ii), printed pp. 69–70.
