# Coefficient squares on polarized affine framed classes

A `CoefficientChange` consists of two \(\mathbf Z_p\)-algebra maps,
one between the affine test rings and one between their reductions.
They commute with the quotient maps. A specified integral polarized
isometry over the new reduced ring compares the extended source of
the framing with the new source. For fixed endpoints, the two ring
maps and the forward coordinate series of this isometry determine
the square.

`mapCoefficients` extends the actual target and its polarization
by the first map. It extends the rational framing section by the
second map and transports it by the source isometry and the
canonical quotient-square isometry on the target. This preserves
order-linearity and the original rational multiplier. Actual
integral isometries of framed triples are preserved, so the map
descends to isomorphism classes.

Ordinary pullback along an affine Nilp map gives a coefficient
square with the same frame at both ends. Its class map agrees with
the existing affine functor. For composition, the target comparison
is the integral polarized isometry for successive coefficient
extensions. On the source, cancellation of the coefficient
composition isometry against its inverse identifies the framing
comparison with the explicit composite. On the reduced target,
identity coordinate series identify the two composites of comparisons.
The rational section extension law then gives the framing square of
the composite isometry. It follows that the class maps compose.

This internal construction generalizes the commuting quotients and
frame comparisons used to define the affine polarized class functor.
It provides the coefficient step for the test twist in Harris
(1997), Appendix (A.4), printed p. 114 (PDF p. 40).
