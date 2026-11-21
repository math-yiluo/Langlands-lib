# Splitting complex Gaussian monomials at the last column

Let `A` be an `m × (m+1)` complex matrix, with `leadingColumns A` its first
`m` columns and `lastColumn A` its final column. A monomial in the real and
imaginary coordinates of `A`, with coefficient `a : ℂ`, is indexed by a finite
support exponent function `d : Coordinates m (m + 1) →₀ ℕ`. The Schwartz test
`gaussianPolynomial (monomial d a)` is this monomial multiplied by
`exp (-∑ i,j, ‖A i j‖²)`.

`ComplexGodementGaussianProductStatement` says that this test is the
`columnProduct` of two Schwartz tests: the leading square Gaussian monomial
with coefficient `a` and exponents `leadingExponents d`, and the column
Gaussian monomial `columnGaussianMonomial` with coefficient `1` and the
remaining exponents. The equality is of Schwartz maps, and includes `m = 0`.
`complexGodementGaussianProduct` proves the statement for every `m`.

## Provenance and scope

This is an internal factorization for the split tests of H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009),
[registered author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf),
§8.3, printed/PDF pp. 58–59. The source uses `Φ(Y,X) = Φ₁(Y)Φ₂(X)` for
square `Y` and last column `X`, and later specializes the square factor to
standard Schwartz tests. The fixed Gaussian here has coefficient `1`
in the exponent, as in `ComplexGodementGaussianPolynomial`, not the `2π`
from Jacquet's definition on p. 10. This construction asserts neither
spanning or density of a family of Whittaker tests nor the functional equation.

## Lean proof

The column Gaussian pulls back the inner-product-space Gaussian along the
real continuous linear equivalence from the column with product norm to the
Euclidean space on the same entries. The column monomial comes from evaluating
a multivariate monomial on the real-linear coordinate selectors; the
resulting multiplier has temperate growth. This gives the actual column
Schwartz map with the stated pointwise product formula.

For a full matrix, split each row's squared norm sum into the leading entries
and the last entry, then sum over the rows. The exponential of the resulting
sum is the product of the two Gaussians. Evaluate the full monomial by a
product over all coordinate indices, since terms missing from its support
have exponent zero. Split that product over column indices using
`Fin.prod_univ_castSucc` and collect the two products over the rows. They
are exactly the evaluations of the two restricted monomials, with the
coefficient placed on the square factor. Multiplying the identities and
using Schwartz map extensionality gives `gaussianMonomial_eq_columnProduct`.
