# Splitting real polynomial Gaussian tests at the last column

The real Godement sections that span the compact-finite standard modules are built from the
polynomial Gaussian tests `gaussianPolynomial p` of `RealGodementGaussianPolynomial`: a complex
polynomial `p` in the entries of an `m × n` real matrix `A`, multiplied by `exp(−Σ A_ij²)`. This
module supplies the facts about these tests that the real adjacent-rank equation needs: the left
orthogonal translates of a test span a finite-dimensional complex space, the same holds for the
square Fourier transform, and a monomial test on `(r+1) × (r+2)` matrices splits into a square
factor and a column factor.

## Left orthogonal translates

- `matrixSqNorm_orthogonal_mul`: for `g` orthogonal, the sum of squares of the entries of `g A`
  equals that of `A`, since it is `trace(Aᵀ A)`.
- `exists_leftTranslate_gaussianPolynomial`: for `g` orthogonal there is a polynomial `q` of total
  degree at most that of `p` with `gaussianPolynomial p (g A) = gaussianPolynomial q A` for all
  `A`. The entries of `g A` are linear forms in the entries of `A`, so `q` is obtained from `p` by
  the substitution `bind₁` of these linear forms, which does not raise the total degree.
- `finiteDimensional_gaussianPolynomial_left`: for any group `K` with a homomorphism
  `iK : K → GL_m(ℝ)` into the orthogonal group, the functions
  `A ↦ gaussianPolynomial p (iK(k)⁻¹ A)` span a finite-dimensional space. They lie in the image of
  the finite-dimensional space of polynomials of total degree at most `p.totalDegree`.

## Fourier transforms

- `finiteDimensional_fourier_left`: if the left translates `X ↦ F(iK(k)⁻¹ X)` of a square Schwartz
  test `F` by an orthogonal family span a finite-dimensional space, so do those of
  `RealGodement.realRectangularSchwartzFourier b F`. By
  `RealGodement.realGodementFourierCovariance`, the transform of the translate
  `rectangularTranslate (iK k)⁻¹ 1 F` is the corresponding translate of the transform, since an
  orthogonal matrix has absolute determinant one and is fixed by the inverse transpose. The
  translates of `F` as Schwartz maps span a finite-dimensional space (the coercion to functions is
  injective), and the transform is linear.

## Splitting at the last column

- `columnMatrixEquiv n`: column vectors of length `n` as `n × 1` matrices.
- `columnGaussianMonomial d`: the row Schwartz test `x ↦ (∏_i x_i^(d_i)) · exp(−Σ_i x_i²)` on
  `ℝ^(r+1)` (`columnGaussianMonomial_apply`).
- `leadingExponents d`: the exponents of a monomial on `(r+1) × (r+2)` matrices restricted to the
  first `r+1` columns.
- `gaussianMonomial_eq_realColumnProduct`: the monomial Gaussian test with exponents `d` and
  coefficient `a` is `realColumnProduct` of the square monomial Gaussian test with exponents
  `leadingExponents d` and coefficient `a`, and the column Gaussian monomial with the exponents
  of the last column. The sum of squares and the monomial both split over the leading columns
  and the last column.
- `gaussianPolynomial_sum_monomials`: a polynomial Gaussian test is the finite sum of the
  Gaussian tests of the monomials of `p`, by linearity of `gaussianPolynomialLinear`.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, p. 58, assumes "as we may" that the Schwartz
function of the Godement section is a product `Φ(Y, X) = Φ₁(Y)Φ₂(X)` of a square and a column
factor, and on p. 59 that `Φ₁` is standard, so that it is reproduced by an elementary idempotent.
For the polynomial Gaussian tests of the Library this module makes both reductions explicit: each
test is a finite sum of monomial tests, each monomial test is such a product, and the left
orthogonal translates of the square factor and of its Fourier transform each span a
finite-dimensional space.
