# Continuous one-parameter groups in a complete normed algebra are exponentials

Module `Langlands.Analysis.OneParameterExponential` proves that continuous homomorphisms from
`ℝ` and from `ℝ^ι` into the multiplicative monoid of a complete normed real algebra are
exponentials, and computes the exponential of a combination of commuting operators on a joint
generalized eigenspace. It is used by `Langlands.Global.FiniteTranslationExponentPolynomials`.
`NormedSpace.exp` is the exponential series of Mathlib.

## Results

Throughout, `𝔸` is a complete normed `ℝ`-algebra.

- `exp_add_of_commute_real`: `exp (x + y) = exp x * exp y` for commuting `x, y ∈ 𝔸`, through
  Mathlib's `exp_add_of_commute_of_mem_ball` over `ℝ` (Mathlib's `exp_add_of_commute` asks for a
  normed `ℚ`-algebra structure).
- `exists_exp_of_continuous_add_mul`: if `M : ℝ → 𝔸` is continuous, `M 0 = 1` and
  `M (s + t) = M s * M t`, then there is `X ∈ 𝔸` with `M t = exp (t • X)` for all `t`, and `X`
  commutes with every element that commutes with all values `M s`.
- `exists_exp_sum_of_continuous_add_mul`: if `M : (ι → ℝ) → 𝔸` (`ι` finite) is continuous,
  `M 0 = 1` and `M (s + t) = M s * M t`, then there are pairwise commuting `X i`, each commuting
  with every `M t`, with `M t = exp (∑ i, t i • X i)`.
- `mem_maxGenEigenspace_sum`: for pairwise commuting endomorphisms `X i` of a complex vector
  space, a vector in the joint maximal generalized eigenspace `⋂ᵢ maxGenEigenspace (X i) (μ i)`
  lies in the maximal generalized eigenspace of `∑_{i ∈ s} c i • X i` for the eigenvalue
  `∑_{i ∈ s} c i * μ i`.
- `exp_sum_smul_apply_of_mem`: on a finite-dimensional complex normed space `E`, for pairwise
  commuting `X i ∈ E →L[ℂ] E` and a joint generalized eigenvector `v` with eigenvalues `μ i`,

  `exp (∑ i, t i • X i) v = exp (∑ i, t i μ i) • ∑_{k < dim E} (k!)⁻¹ • N^k v`,
  `N = ∑ i, t i • (X i - μ i • 1)`.

## Proofs

**One parameter.** By continuity at `0` choose `ε > 0` with `‖M s - 1‖ ≤ 1/2` on `(0, ε]`. Then
`I = ∫₀^ε M` satisfies `‖ε⁻¹ I - 1‖ ≤ 1/2` (`intervalIntegral.norm_integral_le_of_norm_le_const`),
so `ε⁻¹ I` is a unit (`Units.oneSub`) and `I` has a two-sided inverse `J`. Substituting
`s = t + x` and pulling the constant `M t` out of the integral (as a continuous linear map) gives
`∫_t^{t+ε} M = M t * I`. Writing the left side as `F (t + ε) - F t` with `F u = ∫₀^u M`, the
fundamental theorem of calculus (`Continuous.integral_hasStrictDerivAt`) shows that
`M t = (F (t + ε) - F t) * J` is differentiable with derivative `M t * X`,
`X = (M ε - 1) * J`. An element commuting with every `M s` commutes with `I` (integrals commute
with left and right multiplication), hence with `J` and with `X`; in particular every `M t`
commutes with `X`. The function `h t = exp (t • (-X)) * M t` then has derivative
`exp (t • (-X)) * (-X * M t + M t * X) = 0` (`hasDerivAt_exp_smul_const`, product rule), so it is
constant, equal to `h 0 = 1` (`is_const_of_deriv_eq_zero`), and
`M t = exp (t • X) * exp (t • (-X)) * M t = exp (t • X)`.

**Several parameters.** Apply the one-parameter result to `s ↦ M (Pi.single i s)` for each `i`,
obtaining `X i`. The commutation clause shows that `X i` commutes with every `M t` (the values of
`M` commute with each other) and hence that the `X i` commute pairwise. Writing
`t = ∑ᵢ Pi.single i (t i)` (`Finset.univ_sum_single`), induction over finite sets of indices and
`exp_add_of_commute_real` give `M t = exp (∑ i, t i • X i)`.

**Generalized eigenspaces.** `mem_maxGenEigenspace_sum` is an induction over `s` with Mathlib's
`Module.End.genEigenspace_le_smul` and `Module.End.genEigenspace_inf_le_add` at the index `⊤`.
For `exp_sum_smul_apply_of_mem`, write `∑ i, t i • X i = c • 1 + N` with `c = ∑ i, t i μ i`. The
previous lemma, with `maxGenEigenspace_eq_genEigenspace_finrank`, gives `N^{dim E} v = 0`. Since
`c • 1` commutes with `N`, `exp (c • 1 + N) = exp c • exp N` (`algebraMap_exp_comm`,
`Complex.exp_eq_exp_ℂ`), and applying the exponential series of `N`
(`exp_series_hasSum_exp'`) to `v` through the evaluation map `A ↦ A v` gives a series whose terms
vanish from `k = dim E` on, so `exp N v` is the finite Taylor sum.

## Provenance

These are standard facts of the theory of matrix and Banach-algebra exponentials (continuous
one-parameter subgroups of `GL_n` are of the form `t ↦ exp (tX)`); the integral argument for
differentiability is the classical one. They provide the analytic input for the description of
smooth `𝔷(A_M)`-finite functions on `A_M` as exponential polynomials in Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.3.1, printed pp. 40–41.
