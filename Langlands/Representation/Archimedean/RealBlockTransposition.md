# Block Fourier modes and integrals over `O(N)`

Lean module: `Langlands.Representation.Archimedean.RealBlockTransposition`, namespace
`Langlands.Archimedean.RealBlockTransposition`.

## Role and provenance

This module is internal harmonic analysis on the orthogonal group, written for the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. There, the
"F-landing" step shows that a composite of block multiplier maps kills the finite-dimensional
modes. It does so through a duality argument, which needs the results here: the integral over
`O(N)` of a product, written in terms of block Fourier coefficients; the transposition rule for
block multipliers; and the orthogonality of complementary sets of modes. These are standard
facts about Fourier series on the circle `θ ↦ r_p(θ)`, used together with the invariance of
Haar measure. No literature statement is formalized, so the module has no sources.

## Notation

- `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`. `O(N)` is the subgroup `unitaryCompact ℝ N`, with
  the normalized Haar measure `RealPrincipalSeriesDuality.haarK N` (Library).
- `r_p(θ) = blockRotation N p θ` is the rotation in the coordinates `p, p + 1`, with `p + 1 < N`.
- `Φ_j f (g) = blockFourierCoefficient N p j f g = ∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ`, with no
  factor `(2π)⁻¹`.
- "Right `O(N)`-finite" means membership in
  `kFiniteVectors (Whittaker.rightTranslation ℂ (GL_N(ℝ))) (unitaryCompact ℝ N)`.
- `expMode j θ = e^{ijθ}` (Library, `RealBlockFourierFinite`).

The local instances `measurableSpaceK` and `BorelSpace` on `O(N)` are the ones of the Library
module `RealPrincipalSeriesDualityProof`.

## Declarations

- `rotK N p θ`: the rotation `r_p(θ)` as an element of the subgroup `O(N)`.
- `two_pi_ne_zero`: `2π ≠ 0` in `ℂ`.
- `exists_mul_eq_sum`: let `φ, ψ` be continuous and right `O(N)`-finite. There is a bound `D`
  such that for every `D' ≥ D`, every `g ∈ O(N)` and every `θ`,
  `φ(r_p(θ) g) ψ(r_p(θ) g) = (2π)⁻¹ (2π)⁻¹ Σ_{i, j ∈ [-D', D']} Φ_i φ(g) Φ_j ψ(g) e^{i(i+j)θ}`.
- `exists_integral_mul_eq_sum` (**Parseval formula along a block**): for continuous right
  `O(N)`-finite `φ, ψ` there is a bound `D` such that for every `D' ≥ D`,
  `∫_{O(N)} φ ψ = (2π)⁻¹ (2π)⁻¹ Σ_{j ∈ [-D', D']} ∫_{O(N)} Φ_j φ · Φ_{-j} ψ`.
- `integral_mul_eq_of_multiplier` (**transposition**): let `φ, φ', ψ, ψ'` be continuous right
  `O(N)`-finite functions and `μ : ℤ → ℂ` any sequence. Suppose that on `O(N)`, for all `j`,
  `Φ_j φ' = μ(j) Φ_j φ` and `Φ_j ψ' = μ(-j) Φ_j ψ`. Then
  `∫_{O(N)} φ' ψ = ∫_{O(N)} φ ψ'`.
- `integral_mul_eq_zero_of_modes` (**orthogonality**): let `φ, ψ` be continuous right
  `O(N)`-finite and `l : ℕ`. If on `O(N)` `Φ_j φ = 0` for `|j| < l` and `Φ_j ψ = 0` for
  `|j| ≥ l`, then `∫_{O(N)} φ ψ = 0`.

## Proofs

`exists_mul_eq_sum`. The Library lemma `exists_trigPoly_of_mem_kFiniteVectors` gives degrees
`D₁` and `D₂`. For `g ∈ O(N)`, the functions `θ ↦ φ(r_p(θ) g)` and `θ ↦ ψ(r_p(θ) g)` are
trigonometric polynomials of these degrees. Take `D = max D₁ D₂`. For `D' ≥ D` both lie in
`trigPoly D'`. Fourier inversion for trigonometric polynomials (`eq_sum_coeff_of_mem_trigPoly`)
writes each as `(2π)⁻¹ Σ_{j ∈ [-D', D']} Φ_j(·)(g) e^{ijθ}`. Multiply the two sums
(`Finset.sum_mul_sum`) and use `e^{iiθ} e^{ijθ} = e^{i(i+j)θ}` (`expMode_add`).

`exists_integral_mul_eq_sum`. Take `D` from `exists_mul_eq_sum` and fix `D' ≥ D`. Put
`C = ∫_{O(N)} φ ψ` and `A(i, j) = ∫_{O(N)} Φ_i φ · Φ_j ψ`. The block Fourier coefficients of
continuous functions are continuous (Library `RealBlockJacquet.continuous_blockFourierCoefficient`),
so all these integrands are integrable on the compact group (`integrable_of_continuous`).

1. Left invariance of Haar measure (`integral_mul_left_eq_self` with `rotK N p θ`) gives
   `C = ∫_{O(N)} φ(r_p(θ) k) ψ(r_p(θ) k) dk` for every `θ`. Insert the expansion of
   `exists_mul_eq_sum` and exchange the integral with the finite sums. This gives
   `C = (2π)⁻² Σ_{i,j} A(i, j) e^{i(i+j)θ}` for all `θ`.
2. Integrate this identity over `θ ∈ [0, 2π]`. The left side gives `2π · C`. On the right,
   `∫₀^{2π} e^{imθ} dθ` is `2π` for `m = 0` and `0` otherwise (`integral_exp_int_mul`). For each
   `i` only `j = -i` survives, and `-i ∈ [-D', D']`. So
   `2π · C = (2π)⁻² Σ_i A(i, -i) · 2π`. Cancel `2π`.

`integral_mul_eq_of_multiplier`. Apply the Parseval formula to `(φ', ψ)` and to `(φ, ψ')` with
the common index range `D' = max D₁ D₂`. Compare the sums term by term. At every `k ∈ O(N)`,
`Φ_j φ'(k) Φ_{-j} ψ(k) = μ(j) Φ_j φ(k) Φ_{-j} ψ(k)`. Also
`Φ_j φ(k) Φ_{-j} ψ'(k) = Φ_j φ(k) μ(j) Φ_{-j} ψ(k)`, because `μ(-(-j)) = μ(j)`.

`integral_mul_eq_zero_of_modes`. In the Parseval formula, every term
`Φ_j φ(k) Φ_{-j} ψ(k)` vanishes: the first factor if `|j| < l`, the second if `|j| ≥ l`
(then `|-j| ≥ l`).
