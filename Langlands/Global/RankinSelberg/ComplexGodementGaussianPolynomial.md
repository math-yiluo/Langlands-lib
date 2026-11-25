# Compact-finite Gaussian-polynomial tests on complex matrices

For any `m, n : ℕ`, `gaussianPolynomial p` is the complex-valued Schwartz
function on `Matrix (Fin m) (Fin n) ℂ` with value

\[
p((\operatorname{Re} A_{ij},\operatorname{Im} A_{ij})_{ij})\,
  \exp\left(-\sum_{i,j}|A_{ij}|^2\right).
\]

The coordinate index type `Coordinates m n` is `Fin m × Fin n × Bool`;
`false` selects the real part and `true` the imaginary part. The selected
real scalar is included in `ℂ`, and polynomial coefficients are complex.
`gaussianPolynomial_apply` specifies the value. In
`ComplexGodementGaussianPolynomialStatement`, the number of columns is `m+1`.
For each polynomial separately, the complex linear span of the functions
`A ↦ gaussianPolynomial p (A * k)` as `k` varies over the unitary group is
finite dimensional. This is the translate action `translateTest` of the
Library's complex Godement construction. The theorem
`complexGodementGaussianPolynomial` proves the packaged statement.
The same argument proves `finiteDimensional_rightTranslate_gaussianPolynomial`
with arbitrary row and column counts.
`exists_gaussianPolynomial_mul_unitary` gives the translated polynomial
and its total-degree bound.

## Provenance and scope

This is an internal helper for the standard Schwartz tests used in the complex
case of H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
[registered author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf),
printed/PDF p. 10 (definition of standard tests), and §8.3, pp. 58–59 (product
and standard tests in the adjacent-rank induction). Real and imaginary
coordinate polynomials are an alternative to polynomials in entries and their
conjugates, since each pair of coordinates is a complex-linear combination of
the other pair. The exponent here has coefficient `1`, not the coefficient
`2π` of Jacquet's complex standard Fourier normalization; the lemma does not
assert preservation of this family under Jacquet's Fourier transform. It does
not show density or generation of the Whittaker model, prove the product split,
or prove either local functional equation.

## Lean proof

* Take `radialGaussian` on a real inner product space; it is declared, under its
  full name in this module's namespace, in
  [SchwartzGaussian](../../Analysis/SchwartzGaussian.md). The polynomial
  `Q(x) = -‖x‖²` has temperate growth. Its first through `n`th derivatives admit
  a uniform polynomial bound in `1 + ‖x‖`. Since all real derivatives of
  `exp` are `exp`, the iterated composition bound gives an exponential factor
  `exp(Q(x))` times a polynomial bound. The Gaussian decay estimate bounds
  that expression with any extra power of `‖x‖`, as required by each Schwartz
  seminorm. Pull this real Gaussian back along the real continuous linear
  equivalence from matrices to the Euclidean normed space of entries, and
  include its values into `ℂ`.
* Evaluation of a multivariate polynomial on continuous real-linear
  coordinates has temperate growth by induction using constants, addition,
  and multiplication by a variable. Multiplication by this evaluation thus
  preserves the Schwartz property.
* Right multiplication by a unitary matrix preserves the squared norm of
  every row, hence the entire Gaussian. On the polynomial factor it acts by
  substitution of real-linear combinations of the coordinate variables.
  The sum, product, and power degree bounds show that substitution does not
  increase total degree. Therefore each translate belongs to the image,
  under weighted polynomial evaluation, of `restrictTotalDegree` for the
  original degree. That polynomial space is finite dimensional, as are its
  image and the span contained in the image. This also covers empty rows.

The affine-substitution degree bound `totalDegree_bind₁_le` also applies
when the variables are restricted to an upper triangular slice.
