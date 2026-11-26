# Finite sums from real equal-rank polynomial normalizations

For irreducible real standard modules, suppose that every ordinary equal-rank
test with a polynomial Gaussian row has a polynomial normalization and these
tests cover every spectral point. `RealEqualFiniteSumFromPolynomialsStatement`
gives a finite sum of ordinary normalized values equal to one with the
supplied quotient measure and opposite additive scales.

Radial differentiation of a polynomial times a fixed Gaussian preserves
that form. In each coordinate it sends the polynomial factor to its Euler
derivative and differentiates the Gaussian by a quadratic multiplier.
Equality of the ordinary and uniform Whittaker coefficient models supplies
the gauge bounds for the real radial integration identity. Comparing the
polynomial normalizations of the original and differentiated rows on a
common right half-plane yields an affine spectral multiplier. Subtracting
the central-exponent term and dividing by the nonzero rank proves that the
span of the normalized polynomials is closed under multiplication by the
spectral variable. The Library's polynomial generation result then gives
the finite sum, with coefficients absorbed into a Whittaker vector.

This is the algebraic part of the equal-rank argument in H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), §15, pp. 108–109 of the
author-posted version. The polynomial normalization and coverage hypotheses
are the analytic inputs to this reduction.
