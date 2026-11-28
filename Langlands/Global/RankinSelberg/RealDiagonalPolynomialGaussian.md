# Polynomial Gaussian zeta integrals on the real diagonal

`RealDiagonalPolynomialGaussianStatement` integrates a complex polynomial in
\(n\) real coordinates times the product of the standard Gaussians of scale
\(\pi\). The measure is the product additive Lebesgue measure with the Tate
weight \(\prod_i \operatorname{sgn}(x_i)^{e_i}|x_i|^{s+t_i-1}\), represented
by `weightedKernel`. For each choice of test, parities, and shifts, there is a
polynomial \(Q(s)\). For \(\operatorname{Re}(s+t_i)>0\) for all \(i\), the
integral is absolutely convergent with value

\[
Q(s)\prod_i\Gamma_{\mathbb R}(s+t_i+e_i).
\]

`realDiagonalPolynomialGaussian` expands the test into a finite sum of
monomials. Each monomial gives a product of the one-dimensional polynomial
Gaussian Tate integrals. Product integrability comes from the scalar
integrability, and product Fubini computes the integral. Composing each
scalar normalization polynomial with the appropriate shift puts its
variable on the common spectral line. The finite sum has the displayed
product as a common factor.

This is the diagonal calculation used in the square integral argument for
[Jacquet, *Archimedean Rankin–Selberg integrals*, §4.7, pp. 30–31 and §8.4, pp. 60–61](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
