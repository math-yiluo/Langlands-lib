# Split Gaussian tests for the complex rank-gap restriction

The partial Fourier transform of each rectangular Gaussian monomial
has the split form required by `complexGapSplitPartialRestriction`.
Its leading rectangle is a Gaussian monomial in the restricted
coordinates. The first and subsequent physical tail columns use
the corresponding column monomials. The final frequency factor
is the Fourier transform of the last column monomial for the
specified trace character and self-dual measure.

The proof separates the coordinate monomial into column products.
The sum of squared entries also separates by columns, so the Gaussian
becomes the product of the column Gaussians. The established final
column split lets the square factor leave the partial Fourier integral.
Splitting the square columns at the leading block gives the exact
product in `HasSplitPartialTest`.

`splitGaussianMonomial_schwartz` gives Schwartz representatives of
the leading rectangle, first column and last frequency. The
leading representative uses the entrywise norm.

Jacquet’s polynomial-times-Gaussian tests on author p. 10 motivate the
choice of shape. The Lean result uses the Library’s matrix Gaussian
`exp(−∑ᵢⱼ |Aᵢⱼ|²)`. The split uses the positive last-column Fourier
pairing in H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
§10.1, author p. 69, and the arrangement of rectangular and column
factors in §10.2, author p. 72.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
