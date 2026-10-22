# Polynomial approximation in the actual restricted-series norm

Author: Worker 56.

This module uses the one-variable instance of the actual restricted-series
algebra. It imports the polynomial inclusion from
`RestrictedSeriesDefinitions`, proves that its norm is
the supremum of the polynomial coefficient norms, and shows that polynomial
truncations converge in the Gauss norm. The inclusion therefore has dense
range. The coefficient ring is any ultrametric normed commutative ring;
neither completeness nor a field structure is used.

The norm convergence follows directly from the defining condition that the
coefficient sequence tends to zero. After a sufficiently large truncation,
every coefficient of the difference is bounded by half a prescribed positive
error. The coefficientwise characterization of the Gauss norm gives the
required bound. This does not replace the Gauss topology by the weaker
coefficient topology of formal power series.

This is the polynomial-approximation input to analytic Weierstrass division
in Section 2.2, pages 2-3, of the retained Berkovich-course notes. This file
does not prove division or preparation. Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
