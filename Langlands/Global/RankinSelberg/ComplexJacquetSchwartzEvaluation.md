# Canonical Jacquet evaluation of Schwartz Godement sections in a strict chamber

For fixed retained inducing exponents, `complexJacquetSchwartzEvaluation` gives a sufficient bound on the real adjoining exponent. In the strict upper-Borel chamber subject to this bound, suppose a larger compact-finite standard vector equals the Godement section of a rectangular Schwartz test and a smaller standard vector. Its canonical Jacquet value is the continued Godement value applied to the smaller canonical Jacquet value.

The canonical Jacquet maps agree with their open-cell integrals at both ranks in the strict chamber. Substitute these two chamber evaluations and apply the Schwartz open-cell comparison. The identity between entry and operator Schwartz tests gives the same translated function under either norm. At shift zero the extra determinant power is one, so the comparison is exactly `continuedValue` for the actual adjoining character and the chosen integrating character.

This supplies the canonical evaluation of the polynomial Gaussian generators used in the adjacent-rank proof. [Jacquet, *Archimedean Rankin–Selberg integrals*, Proposition 7.2, equation (7.6), and Section 8.3](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
