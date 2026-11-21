# Column factorization of the Gaussian Godement generators

`complexGapGaussianFactors` writes each polynomial Gaussian generator as a finite sum of monomial Gaussian tests. Each monomial has one leading rectangular Schwartz factor and one Schwartz factor for each of the remaining columns.

The proof partitions the polynomial exponents by the leading columns and the individual tail columns. The squared sum of all entries splits by the same partition, and exponentiating its negative gives the product of the Gaussian factors. The polynomial Gaussian linearity then sums the monomials. This supplies the split tests used by the larger rank difference calculation. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
