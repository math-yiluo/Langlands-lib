# Quotient factors in Jacquet’s finite expansions

This internal comparison applies the compact insertion identity to the unfolded integrals in Jacquet §8.2 and §8.3. Each comparison takes a reproducing square test, a finite expansion of the averaged Whittaker coefficient, and the absolute integrability hypotheses for changing the order of integration and separating the factors.

In §8.2 the matrix coefficient is evaluated at the product of the padded smaller-group variable and the full group variable. After the compact insertion, taking the quotient factor of a term gives the ordinary corank-one zeta integral. The exponent is `s − 1/2`, since the group sizes differ by one.

In §8.3 both variables come from the smaller group. The last-row test stays in the quotient factor, which is therefore its ordinary equal-rank zeta integral. Both computations retain the square determinant twist and the corresponding determinant shifts in the matrix factor. The compact translation can be parametrized by either the identity or inverse transpose, so the same comparisons apply to the dual integrals once their averaged coefficients and reproducing identities are supplied.

The proposition `ComplexLocalCompactProductsStatement` proves the compact insertion's fixed-quotient-variable integrability in both comparisons for a Schwartz matrix test and a Whittaker-model coefficient. It applies the common compact insertion estimate with the padded representative in the equal-rank case and the representative itself in the corank-one case. The other factors are constant at each representative. Moving the fixed real determinant shift to the half-plane threshold gives a threshold valid for every representative.
