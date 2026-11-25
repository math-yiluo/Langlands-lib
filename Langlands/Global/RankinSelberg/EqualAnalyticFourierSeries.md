# Fourier series for a family of characters on a compact space

Module `Langlands.Global.RankinSelberg.EqualAnalyticFourierSeries`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

A generic supporting module for Poisson summation on `𝔸^n` and for the classification of additive
characters of `𝔸/F`. It does not mention number fields.

## Provenance

Internal. It is the standard uniqueness and inversion theorem for Fourier series on a compact
group, derived from Mathlib's complex Stone–Weierstrass theorem
(`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`).

## Setting

`X` is a compact Hausdorff space with a Borel σ-algebra and a measure `ν`. `e : ι → C(X, ℂ)` is
indexed by an additive group.

- `IsCharacterFamily e`: `e 0 = 1`, `e (i + j) = e i * e j`, `e (-i) = conj (e i)` and
  `‖e i x‖ = 1`.
- `fourierCoeff ν e f i = ∫ f · conj (e i) dν`.

## Declarations

- `integrable_continuousMap`: continuous functions are integrable for a finite measure.
- `pairingCLM ν g : C(X, ℂ) →L[ℂ] ℂ`, `p ↦ ∫ p · g dν`, with operator norm bound `ν(X) ‖g‖`.
- `characterAlgebra he`: the complex span of the family as a star subalgebra (closed under
  products and conjugation by the character identities). `characterAlgebra_topologicalClosure`:
  if the family separates points, its closure is everything (Stone–Weierstrass).
- `eq_zero_of_fourierCoeff_eq_zero` (for `ν` a probability measure of full support): a continuous
  `f` all of whose coefficients vanish is zero. The kernel of `p ↦ ∫ p · conj f` is closed and
  contains the span, hence contains `f`. So `∫ |f|² = 0`, and continuity together with full
  support gives `f = 0`.
- `integral_mul_star`: if `∫ e i = 0` for `i ≠ 0`, then `∫ e i · conj (e j) = δ_{ij}`.
- `hasSum_fourierCoeff`: if moreover the coefficients of `f` are absolutely summable, then
  `HasSum (i ↦ fourierCoeff ν e f i · e i x) (f x)` for every `x`. The series
  `g = Σ c_i • e i` converges in `C(X, ℂ)`. Its coefficients are `c_j`, by continuity of
  `pairingCLM` and orthogonality. So `f - g` has vanishing coefficients, and evaluation is
  continuous.
