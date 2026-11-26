# The exact real toral quotient density

For \(n\geq 0\), let \(q\mapsto\alpha(q)\) be the logarithmic diagonal
coordinate of the real Iwasawa decomposition on \(N\backslash
\mathrm{GL}_n(\mathbb R)\). For \(y\in\mathbb R^n\), the linear form
`torusModularLog n` is
\[
  M_n(y)=\sum_{i=0}^{n-1}(n-1-2i)y_i .
\]
`realToralQuotientDensity` proves that the pushforward of a compatible
quotient measure by \(\alpha\) has density \(c\exp(-M_n(y))\) with respect
to Lebesgue measure, for a finite constant \(c\geq 0\). The statement
gives the integration formula for every nonnegative measurable integrand.

Conjugating an upper unitriangular matrix by the diagonal of \(e^{y_i}\)
scales entry \(i<j\) by \(e^{y_i-y_j}\). Haar measure on the upper
unitriangular group is proportional to product measure in those entries.
The change of variables therefore multiplies its pushforward by
\(\exp(-M_n(y))\), since index \(i\) occurs \(n-1-i\) times as a row and
\(i\) times as a column. The Weil formula applied to products of a
toral test and an upper unitriangular bump then shows that the toral
measure translates by the multiplier \(\exp(M_n(y))\). Multiplying the
toral measure by that exponential density gives a translation-invariant
measure, hence a multiple of Lebesgue measure.

This is the logarithmic form of the factor \(\delta_n(a)^{-1}\) in the
real quotient integration formula. [Jacquet, *Archimedean Rankin–Selberg integrals*, §3.1, p. 11](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
