# The dual compact profile of an inverse-translation coefficient over the real field

Fix a real block list `ds`, an `O(n)`-finite standard section `f` and an orthogonal matrix
`x`. The finite group `T = (Fin n → ℤˣ)` of sign vectors acts on `O(n)` through the
diagonal sign matrices; on `ds` the inducing character takes the value
`signCharacter ds t` (a product of `±1`) on the sign vector `t`.

`probe f x` is the finite average

`probe f x k = |T|⁻¹ Σ_t (signCharacter ds t)⁻¹ f(k⁻¹ · signMat t · x)`, `k ∈ O(n)`.

* `probe_one`: `probe f x 1 = f(x)`, because `f(signMat t · y) = signCharacter ds t · f(y)`
  (the principal-series covariance of `f` on the sign diagonal), so all terms equal `f(x)`.
* `probe_covariance`: `probe f x (signMat t · k) = (signCharacter ds t)⁻¹ probe f x k`, by
  reindexing the sum along `s ↦ t s`.
* `norm_probe_le`, `norm_probe_sub_le`: the sign characters have norm one, so a uniform bound
  on the compact values of `f`, respectively on `y ↦ f(k⁻¹ y) - f(y)`, also bounds
  `probe f x k`, respectively `probe f x k - f(x)`.

`dualSection f x` is the principal-series extension of `probe f x` with the negated position
exponents (`PrincipalSeriesExtension.extension`). The restriction of `f` to `O(n)` is a
polynomial in the matrix entries (`exists_mvPolynomial_of_mem_kFiniteVectors`), and the
function `(x, k) ↦ f(k⁻¹ x)` has separated variables (`inv_mul_mem_separated`); hence `probe f x`
is a polynomial function on `O(n)` and its extension is smooth. Together with
`probe_covariance` this gives `dualSection_mem`: `dualSection f x` lies in the smooth
principal series of the dual characters `dualChar (realPositionCharacter ds)`.

`RealCompactDualProbeStatement` records, for all `n`, `ds`, standard sections `f, f₀`,
`x ∈ O(n)` and `g ∈ GL_n(ℝ)`:

* `dualSection f x` lies in the dual principal series;
* `dualSection f x 1 = f(x)`;
* `∫_{O(n)} dualSection f x (k) · f₀(k g) dk = ∫_{O(n)} f(k⁻¹ x) · f₀(k g) dk` for the
  normalized Haar measure `haarK n`.

`realCompactDualProbe` proves it. For the last identity, each sign term is moved by the left
invariance of Haar measure under the sign matrix, and the covariance of `f₀` cancels the
sign character.

This is the real counterpart of the Library's `ComplexCompactDualProbe`; the compact diagonal
torus of the complex case is replaced by the finite group of diagonal sign matrices and the
torus integral by a finite average. It is an internal construction for the compact averages of
`RealNormalizedCompactAverage`; the compact integrals it rewrites are pairings by compact Haar
integration, as defined in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7.
