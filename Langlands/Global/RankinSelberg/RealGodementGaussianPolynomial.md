# Polynomial Gaussian tests on real rectangular matrices

This module defines the polynomial-times-Gaussian Schwartz tests `A ↦ p(A) · exp(−∑ᵢⱼ Aᵢⱼ²)` on real `m × n` matrices. The Gaussian has coefficient one. Jacquet's real standard Schwartz functions (*Archimedean Rankin–Selberg integrals*, 2009, p. 10, just before Theorem 2.7) are `P(A) · exp(−π Tr(AᵀA))`, with coefficient `π`. The two families are not the same on fixed coordinates: pulling back a test `p(A) · exp(−∑ᵢⱼ Aᵢⱼ²)` of this module along the dilation `A ↦ √π · A` gives Jacquet's test with polynomial `P(A) = p(√π · A)`, and every Jacquet test arises this way. So the class here is a rescaled, internal analogue of Jacquet's class. Jacquet states that his class is preserved by the Fourier transform with a standard character; nothing is claimed here about the Fourier transform of this class. The module also records the two properties used later: right orthogonal translation keeps the class without raising the degree, and each such test factors through the half-strength Gaussian. It is the real counterpart of the published `ComplexGodementGaussianPolynomial`. For real matrices the polynomial variables are just the `m · n` entries, with no real and imaginary parts.

## Definitions

- `Coordinates m n = Fin m × Fin n` indexes the entries. `coordinates A v` is the entry `A v.1 v.2`, viewed as a complex number.
- `matrixSqNorm A = ∑ᵢ ∑ⱼ Aᵢⱼ²`. `matrixEuclidean m n` is the continuous linear equivalence of `Matrix (Fin m) (Fin n) ℝ` with `EuclideanSpace ℝ (Fin m × Fin n)`. Its squared norm is `matrixSqNorm` (`matrixEuclidean_norm_sq`).
- `scaledGaussian m n t ht` is the Schwartz test `A ↦ exp(−t · matrixSqNorm A)` for `t > 0`. It is the published radial Gaussian on the Euclidean space, pulled back along a rescaled `matrixEuclidean` (`scaledGaussian_apply`).
- `matrixGaussian A = exp(−matrixSqNorm A)`, as a complex number.
- `gaussianPolynomial p` is the Schwartz test `A ↦ p(coordinates A) · matrixGaussian A`, for a complex polynomial `p` in the entries (`gaussianPolynomial_apply`). It is the Gaussian multiplied by the polynomial, a function of temperate growth (`eval_coordinates_hasTemperateGrowth`). It is additive and homogeneous in `p` (`gaussianPolynomial_add`, `gaussianPolynomial_smul`), and `gaussianPolynomialLinear m n` is the resulting complex-linear map.
- `halfGaussian m n` is the Schwartz test `A ↦ exp(−matrixSqNorm A / 2)` (`halfGaussian_apply`).
- `realLinearPolynomial L` is the linear polynomial `∑ᵢ ∑ⱼ L(Eᵢⱼ) Xᵢⱼ` for a real-linear functional `L` on matrices. Here `Eᵢⱼ` is the matrix unit. Its value at `coordinates A` is `L A` (`eval_realLinearPolynomial`), and its total degree is at most one (`totalDegree_realLinearPolynomial`).

## Results

- `exists_gaussianPolynomial_half_factor`: for every `p` there is a Schwartz `Ψ` with `gaussianPolynomial p A = Ψ A · halfGaussian m n A`. Take `Ψ = p · halfGaussian`, using `exp(−s) = exp(−s/2) · exp(−s/2)`.
- `matrixSqNorm_mul_orthogonal`: for `k` in the orthogonal group `unitaryCompact ℝ n`, `matrixSqNorm (A k) = matrixSqNorm A`. The proof writes the sum of squares as `trace (A Aᵀ)` and uses `k kᵀ = 1`. The same invariance follows for `matrixGaussian` and `halfGaussian`.
- `exists_rightTranslate_gaussianPolynomial`: for every `p` and orthogonal `k` there is `q` with `totalDegree q ≤ totalDegree p` and `gaussianPolynomial p (A k) = gaussianPolynomial q A` for all `A`. Take `q = bind₁ (fun v => realLinearPolynomial (entry v ∘ right multiplication by k)) p`. A substitution of polynomials of degree at most one does not raise the total degree, and the Gaussian factor is unchanged.
- `rightTranslate_mem_range`: the same `q` lies in `restrictTotalDegree (Coordinates m n) ℂ (totalDegree p)`. This is a finite-dimensional space of polynomials.
- `RealGodementGaussianPolynomialStatement` collects the translation property and the half-Gaussian factorization for all `m`, `n` and `p`. `realGodementGaussianPolynomial` proves it from the two lemmas above.

## Provenance

These are internal definitions and lemmas. Their scale is an internal choice; the pairing and spanning modules that use them need only this fixed scale. They are used for the reduction to polynomial-times-Gaussian Schwartz tests that Jacquet, *Archimedean Rankin–Selberg integrals* (2009), makes in Proposition 7.1(vi) (pp. 43 and 46–47) and in Section 8.3 (pp. 58–60). Jacquet's standard tests (p. 10) use the Gaussian `exp(−π Tr(AᵀA))`, so Jacquet's tests are the pullbacks of the tests here along `A ↦ √π · A` (with the polynomial pulled back too), not the same functions. They follow the published complex module `ComplexGodementGaussianPolynomial`.
