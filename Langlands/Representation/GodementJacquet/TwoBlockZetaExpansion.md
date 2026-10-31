# Finite product expansion of two-block induced matrix zeta integrals

Module `Langlands.Representation.GodementJacquet.TwoBlockZetaExpansion`.
Author: Worker 1112.

This module proves the forward half of Godement–Jacquet, *Zeta Functions of Simple
Algebras* (1972), Theorem 3.4 (printed 38–41) for two blocks over a canonical
p-adic field: the shifted matrix zeta integral of an actual bi-smooth coefficient of
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ` is a finite sum of
products of block matrix zeta integrals. The implemented route uses the compact
coefficient formula of `CompactProductCoefficients` (Worker 704) instead of the
source's integration over `P \ G`.

Notation: `t + 1 = (m 0 + 1) + (m 1 + 1)`, `n₀ = m 0 + 1`, `n₁ = m 1 + 1`,
`L = (a, d)` a Levi element, `|·|` the canonical normalized absolute value, shifts
`jpssShift n = n / 2`.

## Exponent bookkeeping

- `weight_identity`: for positive reals `A, D` and `t + 1 = n₀ + n₁`,
  `(A D)^(s + t/2) · (A^(n₁) / D^(n₀))^(1/2) · A^(-n₁) = A^(s + m₀/2) · D^(s + m₁/2)`,
  proved by writing every factor as an exponential of a multiple of `log A`,
  `log D`.
- Definitions `halfModulus F h L = δ_P(L)^(1/2)` (the complex number appearing in
  `normalizedProductInduced_covariant`) and `blockAbs F h L i = |det (L i)|`;
  `halfModulus_eq` evaluates `δ_P(a, d) = |det a|^(n₁) / |det d|^(n₀)` from
  `leviModulus_apply`.
- `normalizedAbs_det_eq_one_of_mem` (via
  `determinantNorm_eq_one_of_mem_compact`) and `determinantWeight_mul_of_mem`:
  two-sided translation by a compact subgroup does not change `|det g|^s`.
- `levi_weight_identity`: `|det parabolicPoint (L, x)|^(s + t/2) · δ_P(L)^(1/2) ·
  |det a|^(-n₁) = |det a|^(s + m₀/2) |det d|^(s + m₁/2)`.

## Levi integrals

For block functions `c₀, c₁`, the definition `leviCoefficientWeight F h c₀ c₁ s L =
|det L|^(s + t/2) δ_P(L)^(1/2) c₀(a) c₁(d)`.

- `leviCoefficientWeight_mul`: `α₀(a) α₁(d) · leviCoefficientWeight · |det a|^(-n₁)`
  is the product of the block integrands `Padic.matrixIntegrand F α₀ (s + m₀/2) c₀ a`
  and `Padic.matrixIntegrand F α₁ (s + m₁/2) c₁ d`.
- `integrable_leviCoefficientWeight`: if every block test converges against `c₀` at
  `s + m₀/2` and against `c₁` at `s + m₁/2`, then for every Schwartz–Bruhat `α` on
  `Mat_{n₀} × Mat_{n₁}` the function `L ↦ α(a, d) · leviCoefficientWeight · |det a|^(-n₁)`
  is integrable (tensor expansion of `α` and `integrable_pi_two_mul`). This is the
  hypothesis of `integral_testFunction_parabolicPoint`.
- `integral_leviCoefficientWeight`: for `Θ(L) = ∑ r, Ψ₀ r a · Ψ₁ r d`, the Levi integral
  of `Θ · leviCoefficientWeight · |det a|^(-n₁)` equals
  `∑ r, Z₀(Ψ₀ r, s + m₀/2, c₀) Z₁(Ψ₁ r, s + m₁/2, c₁)` (`integral_pi_two_mul`).
- `continuous_leviCoefficientWeight`, `continuous_determinantWeight'`.

## Abstract expansion

`exists_zeta_expansion_of_kernel`: let `K` be a compact open subgroup with
`GL_(t+1) = P K`, `ν` a finite measure on `K` (Borel), `Γ : K → GL_(t+1) → ℂ` jointly
continuous, `φ j ∈ SchwartzBruhat (K × K)` and continuous block functions `c₀ j`,
`c₁ j` with
`Γ k (parabolicPoint (L, x) * k') = δ_P(L)^(1/2) ∑ j, φ j (k, k') c₀ j (a) c₁ j (d)`.
For every full-matrix test `Φ` there are a finite type `ι`, constants `w`, block
tests `Ψ₀, Ψ₁` and indices `jj`, all independent of `s`, such that for every `s` at
which all block tests converge against all `c₀ j` (at `s + m₀/2`) and `c₁ j` (at
`s + m₁/2`), the coefficient `g ↦ ∫ k, Γ k (k g) dν` satisfies
`Padic.MatrixConverges F Φ (s + t/2)` and
`Padic.matrixIntegral F Φ (s + t/2) = ∑ i, w i · Z₀(Ψ₀ i, c₀ (jj i)) · Z₁(Ψ₁ i, c₁ (jj i))`.

Proof.
1. `exists_matrixTranslate_expansion` writes `Φ (k⁻¹ X k') = ∑ l, χ l (k, k') Φ_l (X)`
   with `Φ_l = matrixTranslate Φ (r l).1⁻¹ (r l).2`, and
   `exists_upperBlockIntegral_expansion` writes each `Φ_l^P = ∑ r, Ψ₀ l r ⊗ Ψ₁ l r`
   (with `dx = Measure.addHaar`).
2. With `H g = Φ g · |det g|^(s + t/2)`, the integrand is `H g · ∫ k, Γ k (k g) dν`.
   Using `|det k| = 1`, `H (k⁻¹ parabolicPoint z k') Γ k (parabolicPoint z k')` equals
   `∑_{(l, j)} (χ l φ j)(k, k') · Q_{l j}(z)` with
   `Q_{l j}(z) = Φ_l(parabolicPoint z) · leviCoefficientWeight (c₀ j) (c₁ j) z.1`.
3. `CompactFactorization.integrable_integral_coefficient_of_expansion` (with the
   factorization data of `TwoBlockParabolicHaar`, `ν' = comap val μ` on `K`, whose
   pushforward is `μ|_K`) gives integrability and
   `∫ = (parabolicMeasure (parabolicPoint ⁻¹' K))⁻¹ ∑ (∫ χ l φ j d(ν × ν')) ∫ Q_{l j}`.
   Integrability of `χ l φ j` holds since `K × K` is compact; integrability and the
   value of `∫ Q_{l j}` come from `integral_testFunction_parabolicPoint` and the Levi
   lemmas above.
4. Reindexing the finite sums over `Σ l, Fin (R l) × Fin N` gives the result with
   `w = C⁻¹ ∫ χ l φ j`.

## Representation-theoretic instance

`exists_twoBlock_zeta_expansion F h σ hσs hσa Φ ℓ v`: for smooth admissible blocks,
the bi-smooth coefficient `biSmoothCoefficient π ℓ v` of
`π = F.canonicalNormalizedProductInduced (succBlockShape m h) σ` has the same
conclusion, with block coefficients that are actual elements of
`biSmoothMatrixCoefficients (σ i)`, under the hypothesis that all block bi-smooth
coefficients converge at the block shifts. Proof: Worker 704's
`exists_compactProductCoefficientFormula` gives `K`, the factorization `G = P K`, a
Haar probability `μK` on `K` and an equivalence `E` with
`biSmoothCoefficient π ℓ v g = ∫ k, ⟨E ℓ (k), v (k g)⟩ dμK`;
`exists_compactProductPairing_expansion` expands `⟨E ℓ (k), (⊗σ)(L) v (k')⟩` as
`∑ j, φ j (k, k') ∏ i, c_{j i}(L i)`; the covariance
`normalizedProductInduced_covariant` at `parabolicPoint (L, x)` (whose Levi
projection is `L`) supplies `δ_P(L)^(1/2)`. The kernel is jointly continuous because
section evaluations are locally constant, and block coefficients of smooth vectors
are locally constant (`matrixCoefficient_isLocallyConstant`). Then apply
`exists_zeta_expansion_of_kernel`.

`twoBlock_forward_generatorInputs F h σ hσs hσa P hblock`: if both blocks satisfy
`Padic.MatrixAnalyticAssertions F (σ i) (P i)`, then (1) there is one `a` with
`MatrixConverges … Φ (s + t/2) (biSmoothCoefficient π ℓ v)` for all `Φ, ℓ, v` and
`Re s > a` (take `a = max a₀ a₁` of the block half-planes), and (2) every such
coefficient has an actual shifted rational value `R` lying in
`zetaSpan (block 0 values) * zetaSpan (block 1 values)`: with block rational values
`R₀ i, R₁ i`, take `R = ∑ i, C(w i) R₀ i R₁ i`; the continuation follows from
`HasRationalContinuation.mul`, `hasRationalContinuation_const_mul`,
`continuation_sum` and agreement on a right half-plane. These are the first two
components of Worker 704's `TwoBlockMatrixGeneratorInputs`.

## Scope

Only individual actual coefficients `biSmoothCoefficient π ℓ v` are treated;
extension to the whole coefficient span, the reverse inclusion and the normalized
generator are handled elsewhere (`TwoBlockAnalyticAssembly`). No irreducibility,
Whittaker or functional-equation hypothesis is used.
