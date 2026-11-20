# Power sums over the zeros of a holomorphic family in one variable

Module `Langlands.Analysis.SeveralComplex.ZeroCounting`, namespace
`Langlands.Analysis.SeveralComplex`.

`P` is a complex normed space (finite-dimensional except in the first and third items), `F` a
complex Banach space and `Λ` an arbitrary index type. Points of `P × ℂ` are written `(w, t)`.
The `t`-derivative of `H : P × ℂ → ℂ` is expressed as the directional derivative
`fderiv ℂ H (w, t) (0, 1)`.

## Results

- `hasDerivAt_slice`: if `H` is complex differentiable at `(w, t)`, then `s ↦ H (w, s)` has
  derivative `fderiv ℂ H (w, t) (0, 1)` at `t`.
- `differentiableOn_circleIntegral_div_smul`: let `H, K : P × ℂ → ℂ` and `Ψ : P × ℂ → G` be
  complex differentiable on `O ⊆ P × ℂ`, `W ⊆ P` open and `ρ > 0`, and suppose that for
  `w ∈ W` and `|t| = ρ` we have `(w, t) ∈ O` and `H (w, t) ≠ 0`. Then
  `w ↦ ∮_{|t| = ρ} (K (w, t) / H (w, t)) • Ψ (w, t) dt` is complex differentiable on `W`.
- `circleIntegral_slice_eq` (**argument principle for a slice**): let `O` be open, and let
  the scalar function `H : P × ℂ → ℂ` and the vector-valued function `Ψ : P × ℂ → F` (`F` a
  complex Banach space) be complex differentiable on `O`. Fix `w` and an open `v ⊆ ℂ` with
  `(w, t) ∈ O` for `t ∈ v`, `closedBall 0 ρ ⊆ v` (`ρ > 0`) and `H (w, t) ≠ 0` for `|t| = ρ`.
  Then

  `∮_{|t| = ρ} (fderiv ℂ H (w, t) (0, 1) / H (w, t)) • Ψ (w, t) dt
     = 2πi • ∑ᶠ u, D(u) • Ψ (w, u)`,

  where `D = divisor (s ↦ H (w, s)) (closedBall 0 ρ)` is the divisor of the scalar slice
  `s ↦ H (w, s)` on the closed disc. Its integer values, cast to `ℂ`, act as complex scalars
  on the vectors `Ψ (w, u)`.
- `exists_powerSum_family` (**power sums over zeros, holomorphic in the parameter**). Let `P` be
  finite-dimensional, `O ⊆ P × ℂ` open, `H : P × ℂ → ℂ` and `b l : P × ℂ → F` (`l : Λ`) complex
  differentiable on `O`, and `ρ > 0` with `(0, t) ∈ O` for `|t| ≤ ρ` and `H (0, t) ≠ 0` for
  `|t| = ρ`. Then there are `k : ℕ`, `δ > 0` and maps `T l : P → (Fin k → F)`, each complex
  differentiable on `ball 0 δ`, with the following property. Let `w ∈ ball 0 δ` and `s₀ ⊆ Λ`
  be such that every `T l w` lies in the span of `{T μ w | μ ∈ s₀}`. Then for every `t` with
  `|t| < ρ` and `H (w, t) = 0`, and every `l`, the vector `b l (w, t)` lies in the span of
  `{b μ (w, t) | μ ∈ s₀}`.

## Proofs

- `hasDerivAt_slice`: chain rule for `s ↦ (w, s)`, whose derivative is `(0, 1)`.
- `differentiableOn_circleIntegral_div_smul`: the integrand is complex differentiable, hence
  continuous, on `{p ∈ O | H p ≠ 0}`, which contains `W × sphere 0 ρ`; apply
  `differentiableOn_circleIntegral_of_continuousOn` (module `ParametricHolomorphy`).
- `circleIntegral_slice_eq`: on the circle, `fderiv ℂ H (w, t) (0, 1)` equals the derivative of
  the slice `s ↦ H (w, s)` (by `hasDerivAt_slice`), so the integral is the weighted argument
  principle `circleIntegral_logDeriv_smul` (module `ArgumentPrinciple`) applied to the slice and
  to `s ↦ Ψ (w, s)`, both complex differentiable on `v`.
- `exists_powerSum_family`:
  1. Two applications of the tube lemma (`generalized_tube_lemma`) to the compact sets
     `{0} × closedBall 0 ρ ⊆ O` and `{0} × sphere 0 ρ ⊆ {p ∈ O | H p ≠ 0}` give `δ₀ > 0` and an
     open `v ⊇ closedBall 0 ρ` such that for `w ∈ ball 0 δ₀`: `(w, t) ∈ O` for `t ∈ v`, and
     `H (w, t) ≠ 0` for `|t| = ρ`.
  2. `K p = fderiv ℂ H p (0, 1)` is complex differentiable on `O`
     (`differentiableOn_fderiv_apply`, module `LineDerivative`; `P × ℂ` is finite-dimensional).
  3. For `w ∈ ball 0 δ₀` let `D_w` be the divisor of `s ↦ H (w, s)` on `closedBall 0 ρ`. It is
     nonnegative with finite support. Let `N(w) = ∑ᶠ u, D_w(u)` be the number of zeros counted
     with multiplicity. By `circleIntegral_slice_eq` with `Ψ = 1`,
     `(N(w) : ℂ) = (2πi)⁻¹ ∮ K/H`. This is holomorphic, hence continuous, in `w`, so the
     integer `N(w)` is constant, equal to `k = N(0)`, on a ball `ball 0 δ` (`δ ≤ δ₀`): an
     integer within distance `< 1` of `N(0)` equals `N(0)`.
  4. `T l w j = (2πi)⁻¹ ∮_{|t| = ρ} (K (w, t) / H (w, t)) • (t^j • b l (w, t)) dt`,
     `j < k`. It is holomorphic on `ball 0 δ` coordinatewise by
     `differentiableOn_circleIntegral_div_smul`. By `circleIntegral_slice_eq`,
     `T l w = powerSumVector k S D_w (u ↦ b l (w, u))`, where `S` is the support of `D_w`
     (module `PowerSumInterpolation`).
  5. For `w ∈ ball 0 δ`, a zero `t` of `H (w, ·)` with `|t| < ρ` lies in `S` with `D_w(t) ≠ 0`
     (`divisor_closedBall_ne_zero_iff`). Moreover `card S ≤ ∑_{u ∈ S} D_w(u) = N(w) = k`,
     since `D_w ≥ 1` on its support. `mem_span_of_powerSumVector_mem_span` then turns the span
     condition on the `T l w` into the span condition on the `b l (w, t)`.

## Provenance

Internal. The construction (power sums of the zeros of a holomorphic function, expressed by the
argument principle as integrals depending holomorphically on parameters) is the classical
device used in the local theory of analytic sets in place of Weierstrass division. It is
written here as the dimension-reduction step for the proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`
(Bernstein–Lapid, Theorem 3.3) in module `PointwiseSpan`. The Lean proof follows the route
described above and uses only Mathlib and the modules named above.
