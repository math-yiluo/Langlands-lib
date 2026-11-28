# Polynomial Gaussians in the real Tate integral

`RealTatePolynomialGaussianStatement` says that the real Tate integral of
\(P(x)e^{-\pi x^2}\), for a complex polynomial \(P\) and a parity \(e\in\{0,1\}\), agrees with
\(Q(u)\Gamma_{\mathbb R}(u+e)\) for a complex polynomial \(Q\) on \(\operatorname{Re}u>0\).
The measure is Lebesgue measure in the additive coordinate, and the integrand
has the weight \(\operatorname{sgn}(x)^e |x|^{u-1}\).

`monomialGaussian` uses the real polynomial Gaussian construction, and
`polynomialGaussian` takes the finite complex linear combination of those
Schwartz functions with coefficients from \(P\). The proof computes the
monomial integral by two-step induction. Reflection cancels the base cases
of opposite parity, and the adapted Gaussian formula gives the matching cases.
Multiplication by \(x^2\) shifts the Mellin parameter by two, so the gamma
recurrence multiplies the shifted polynomial by \((u+e)/(2\pi)\). Finite
linearity finishes the calculation.

This scalar calculation supplies the starting case of the polynomial
normalization used in Proposition 8.1. [Jacquet, *Archimedean Rankin–Selberg integrals*, §8.4, pp. 60–61](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
