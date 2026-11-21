# Column products of complex Gaussian-polynomial tests

`ComplexGodementGaussianColumnSplitStatement` expresses each Gaussian-polynomial
Schwartz test on `m × (m + 1)` complex matrices as a finite sum of
`ComplexGodementColumnProduct.columnProduct` tests. The factors are
Gaussian polynomials on the leading square block and on the last column.
For every square factor, the span of its translates `A ↦ Φ(k⁻¹ A)` for
`k ∈ U(m)` is finite dimensional. The theorem applies to the Library's fixed
Gaussian `exp(-∑ i,j, |Aᵢⱼ|²)` and all natural numbers `m`, including zero.

## Proof and provenance

The polynomial splitting uses induction on constants, sums, and multiplication
by a variable. A constant is a product with column factor one. For a sum,
concatenate the two finite lists of products. The column index of a variable
is either a leading index or the last index, so multiplication places that
variable in the corresponding factor. Splitting the sum of squared entries
factors the Gaussian. The last-column factor is a Schwartz test via the
real continuous linear equivalence from vectors to one-column matrices.

The left unitary translates of each square factor lie in a finite-dimensional span by `ComplexGodementGaussianProduct.finiteDimensional_gaussianPolynomial_left`. Its proof uses the polynomial coordinates in the matrix entries and their conjugates.

This is an internal lemma for the product choice preceding (8.3) and the
left-unitary averaging of the square factor in §8.3, author-edition pp. 58–59,
of H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009). The standard
Schwartz tests are described on p. 10. The lemma supplies these steps for the
Library's Gaussian and coordinate convention.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
