# Column factorization of the real square Gaussian tests

This module is the real counterpart of the Library's `ComplexGapGaussianFactors`. Let `n = k + q + 1`.
The square Gaussian tests are the Schwartz functions `gaussianPolynomial p` of
`RealGodementGaussianPolynomial`: a complex polynomial `p` in the entries of a real `n × n` matrix
`A` times `exp(-∑_{i,j} A_{ij}²)`.

* `gaussianFactors k q d c f` is the `GodementColumnFactors k q` (see `RealGapAlternateRestriction`)
  whose leading factor is the Gaussian monomial `c · ∏ A_{ij}^{d(i,j)} · exp(-∑ A_{ij}²)` in the first
  `k` columns. For `j ≤ q`, its tail factor `j` is the column Gaussian monomial
  `RealJacquet.columnGaussianMonomial` with exponents `d(·, k + j)`. Its last tail factor `q + 1` is the
  given Schwartz test `f`.
* `gaussianPolynomial_eval_factors`: for every exponent vector `d`, coefficient `c`, test `f` and square
  matrix `A`, `gaussianPolynomial (monomial d c) A = squareEval (gaussianFactors k q d c f) A`.
  The monomial and the Gaussian both split as products over the leading block and the tail
  columns.

`RealGapGaussianFactorsStatement` (proved by `realGapGaussianFactors`): every square Gaussian test
`gaussianPolynomial p` is the finite sum over the support of `p` of the monomial tests
`gaussianPolynomial (monomial d (p.coeff d))`, by `RealJacquet.gaussianPolynomial_sum_monomials`, and
each of these equals `squareEval` of `gaussianFactors k q d (p.coeff d) f` for every `f`.

Combined with `RealGodementPaddedRestriction.realColumnProduct_joinLastColumn`, this makes each
separated test `realColumnProduct (gaussianPolynomial (monomial d c)) f` an admissible test for the
alternate split formula of `RealGapAlternateRestriction`. These are examples of the tests that are
products of a leading factor and column factors, introduced in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §10.2, p. 72, and used in the alternate formula (10.6), p. 73. The Library's Gaussian
`exp(−∑ A_{ij}²)` differs by a change of scale from the standard Gaussian `exp(−π ∑ A_{ij}²)` of the source
(p. 10). By Proposition 7.1(vi), p. 43, under the convergence condition (7.2), `Re(u_n − u_i) > −1` for
`1 ≤ i ≤ n − 1`, every `K_n`-finite vector of the induced representation is a finite sum of Godement sections
(7.1) of standard rectangular Schwartz functions and `K_{n−1}`-finite inputs; the proof on pp. 46–47 also gives density of these sections in the
smooth induced representation.
