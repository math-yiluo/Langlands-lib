# One-coordinate denominators for actual unramified operator families

`rationalUnramifiedCoordinateSlice` uses a supplied integral basis of the
actual valuation image. It fixes the tail coordinates at specified complex
units and preserves the first coordinate. Specialization of any actual
regular scalar along this slice is the pullback of a one-variable Laurent
polynomial. The proof separates out the first exponent in the Laurent
algebra and evaluates the remaining exponents at the fixed tail values.

`continuation_cross_eq_coordinateSlice` takes one actual rational operator
continuation on a nonempty open starting region and the equality of its
starting operators at parameters with the same first coordinate. Choose
the tail of one starting parameter. On the open set of starting parameters
whose sliced value still belongs to the starting region, the equality
identifies the two cleared operator numerators after cross-multiplication.
This open set contains the chosen parameter. The polynomial identity
theorem extends the cross-multiplication to the ambient torus. The sliced
numerator is polynomial per input vector, and the sliced scalar
denominator is nonzero at the chosen parameter. It is selected before
input vectors are used.

This derived reduction is for the one-coordinate dependence of a maximal
parabolic operator discussed after IV.1(13), printed p. 283 / PDF p. 49, and
the pole argument of Corollary V.2.3 and Lemma V.3.1, printed pp. 294–295 /
PDF pp. 60–61, in Waldspurger (2003), `waldspurger-2003-plancherel`.
The dependence and the initial rationality are inputs.
