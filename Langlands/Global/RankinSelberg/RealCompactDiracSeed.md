# A compact-finite seed vector built from corner minors

Module `Langlands.Global.RankinSelberg.RealCompactDiracSeed`, namespace
`Langlands.Global.RankinSelbergGlobal.RealCompactDirac`.

Notation: `Δₗ(X) = corner X l` is the lower-right corner minor on the positions `l, …, n - 1`
(module `RealCompactDiracCorner`), with `Δₙ = 1`; `p : ℕ → ℕ` and `m : ℕ`.

## Definitions

* `signPart p X = ∏_{l < n} (Δₗ(X) Δₗ₊₁(X))^{p l}`.
* `cornerProduct X = ∏_{l < n} Δₗ(X)`.
* `seedReal p m X = signPart p X · (cornerProduct X)^{2m}`, a polynomial in the entries of `X`.
* `seedFunction p m : GL_n(ℝ) → ℂ` and `seedProfile p m : O(n) → ℂ`: `seedReal p m` on
  `GL_n(ℝ)` and on `O(n)`, as complex numbers.
* `seedVector p m e = extension (shiftedExponent n e) (seedProfile p m)`, with the Library's
  `PrincipalSeriesExtension.extension`.

## Results

* `seedFunction_eq`, `seedFunction_mem_kFiniteVectors`: `seedFunction p m` is a product of the
  Library's minor functions `RealTiedMinorProduct.minorG`, which are compact-finite
  (`minorG_mem_kFiniteVectors`); compact-finite functions are closed under products
  (`RealTiedMinorProduct.mul_mem_kFiniteVectors`, `prod_mem_kFiniteVectors`,
  `pow_mem_kFiniteVectors`, `one_mem_kFiniteVectors`).
* `continuous_seedProfile`, `finiteDimensional_seedProfile`: the profile is continuous and its
  right translates span a finite-dimensional space (`RealTiedMinorProduct.finiteDimensional_restrict`).
* `seedReal_signDiagonal`: for `σ_i = signReal(d_i)`,
  `seedReal p m (diag(σ) X) = (∏ₗ σₗ^{p l}) · seedReal p m X`. Left multiplication by `diag(σ)`
  multiplies `Δₗ` by `τₗ = ∏_{i ≥ l} σ_i`; then `τₗ τₗ₊₁ = σₗ` and `(∏ₗ τₗ)^{2m} = 1`.
* `char_signUnit`, `principalSeriesCharacter_signUnit`: if `χ_l(1) = 1` and
  `χ_l(-1) = (-1)^{p l}`, then `χ_l(sgn x) = sgn(x)^{p l}` and the Library's
  `principalSeriesCharacter ℝ n χ (sgn a) = ∏ₗ sgn(a_l)^{p l}`.
* `seedProfile_signDiagonal`: the sign covariance
  `φ₀(signDiagonal(a) κ) = principalSeriesCharacter ℝ n χ (sgn a) · φ₀(κ)` required by the
  Library's extension lemmas.
* `seedVector_mem`: if `IsSignedPower χ e` and `χ_l(-1) = (-1)^{p l}`, then `seedVector p m e`
  lies in `kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)` (Library
  `extension_mem_kFiniteFunctions`).
* `seedVector_unitary`: on `O(n)` the seed vector is the seed profile.

## Provenance

Derived, internal construction. It replaces the spherical seed `f_σ` of Bernstein–Krötz,
*Smooth Fréchet globalizations of Harish-Chandra modules*, arXiv:0812.1684v3, §12.1.3
(Lemma 12.1), by a seed in an arbitrary sign sector: `cornerProduct` is zero exactly where a
corner minor vanishes, that is, off the big cell `B N̄`, and the factor `signPart` carries the
sign character. This is the construction
outlined in step 7 of `RealStandardCompactDirac.md`.
