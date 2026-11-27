# Last-row localization on real unipotent quotients

The real lower-block chart writes a quotient point in a set of full measure as the
class of a block matrix with invertible leading block `g` and last row `(x,u)`.
The lower-block representative is the product of `diag(g,1)` with the section
whose leading block is the identity. For a continuous left-unipotent-invariant
coefficient, `integral_lastRow` applies the chart measure and Fubini to integrate
first over the leading-block quotient with density `|det g|⁻¹`. The second
integral uses Lebesgue measure in `x` and multiplicative Haar measure in `u`.
The comparison scalar is positive and independent of the last-row test.

`realOrdinaryRowLocalization` starts with an integrable invariant coefficient
and assumes continuity of its leading-block integral at the standard row
`(0,1)`. The formula gives an integrable row density. Extending that density
by zero at `u = 0` and multiplying it by `|u|⁻¹` converts its Fourier moments
to the ordinary Euclidean Fourier transform. If all the moments vanish,
Fourier inversion at the standard row gives zero there. The density factor
is one at that row.

The quotient measure formula is the one in Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), §14.2, proof of Lemma 14.1, author-posted p. 106. The
localization in the last row is used in §6.2, Propositions 6.1 and 6.2,
author-posted pp. 41–42.
