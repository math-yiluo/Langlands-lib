# Norm-one Levi pairings of twisted finite expansions

`heightPower_normOneLevi_mul_self` proves that the Iwasawa height power is constant
along the left translates of an ambient point by norm-one Levi points. The Levi
map to the parabolic sends norm-one points to norm-one points. Their logarithmic
character functional is zero. The left multiplication formula for Iwasawa height
then leaves the height unchanged.

`leviPairing_parameterTwist` therefore takes the height twist out of the actual
norm-one Levi integral. `leviPairing_finsetSum` integrates a finite expansion
term by term when the fixed pairing integrands are integrable.
`twistedLeviPairingExpansion` is the resulting height power times the finite
sum of coefficients multiplied by the fixed pairings. The comparison theorem
identifies it with the pairing of the twisted function itself.

`exists_twistedLeviPairingExpansion_extension` assumes a complex-linear parameter
map and one scalar factor that gives holomorphic extensions of the coefficients,
with agreement on the indicated set. Insert those extended coefficients into the
finite pairing expansion. The height power is the exponential of a complex-linear
function at the fixed adelic point. Holomorphy of the expansion follows from the
products and finite sums, and linearity proves agreement after multiplication by
the same scalar factor.

This is a derived part of the comparison between the norm-one pairing in (6.8)
and the twisted terms in (6.18) in Bernstein–Lapid, *On the meromorphic continuation
of Eisenstein series*, §§6.2 and 6.10. The finite expansion and integrability premises
are supplied. The module implements the effect of pairing such terms.

`leviPairing_const_mul` takes a constant scalar outside the normalized Levi pairing.
