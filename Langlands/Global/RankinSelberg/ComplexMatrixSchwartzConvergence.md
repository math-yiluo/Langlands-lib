# Height-weighted complex Schwartz matrix integrals

`ComplexMatrixSchwartzConvergenceStatement` gives absolute convergence of a square Schwartz matrix test on
\(GL_n(\mathbb C)\) multiplied by the \(M\)-th power of Jacquet's height and
the normalized absolute determinant to a complex power \(s\). The measure is
the determinant-density Haar measure. The sufficient half-plane is
\(\operatorname{Re}(s)\ge n+M\).

The proof multiplies the height by the squared determinant norm and uses
the adjugate to express the result as a polynomial in real matrix
coordinates. After accounting for the Haar density and this determinant
power, the remaining determinant exponent in the absolute integrand is
nonnegative. It is bounded by an integer power of one plus the squared
determinant norm. The polynomial bounds have temperate growth, so their
product with a Schwartz test is integrable on the additive matrix space.
The determinant-density criterion transfers this domination to the
multiplicative integral.

This gives the Schwartz-test conclusion of Lemma 3.3(ii) in the complex
case with a concrete sufficient threshold. [Jacquet, *Archimedean Rankin–Selberg integrals*, Lemma 3.3, p. 13](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
