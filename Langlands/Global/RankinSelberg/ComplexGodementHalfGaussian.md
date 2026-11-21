# Half-strength Gaussian integrability for unitary Godement samples

`godementPolynomialGaussian` transports the Library's polynomial Gaussian Schwartz test to the operator matrix norm by the identity continuous linear equivalence. The specialization at polynomial \(1\) and scale \(1/2\) has value \(\exp(-\sum_{i,j}|X_{ij}|^2/2)\).

`complexGodementHalfGaussian` applies standard-module Godement convergence to this Schwartz test at the identity. Right unitary multiplication preserves the squared norm of each row. The trailing rows of a unitary matrix are the trailing rows of the identity multiplied by that matrix, so the same Gaussian value occurs at every unitary sample. The weighted integrand on the product measure therefore equals the product of the integrable sample weight and the single identity integrand. Haar uniqueness permits any smaller-group Haar normalization.

The bound on the adjoining character exponent is the one supplied by `complexGodementStandardConvergence`. The joint estimate prepares the use of Gaussian moments when passing from Godement generators to the split tests in the adjacent-rank unfolding. [Jacquet, *Archimedean Rankin–Selberg integrals*, Proposition 7.1(i) and Section 8.3](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
