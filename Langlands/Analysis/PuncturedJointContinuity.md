# Joint continuity across a removable point

Module `Langlands.Analysis.PuncturedJointContinuity` proves one lemma of complex analysis with a
parameter in a topological space.

## Statement

`Langlands.Analysis.exists_ball_continuousOn_of_punctured`. Let `X` be a topological space,
`W ⊆ ℂ` open, `s₀ ∈ W` and `f : ℂ → X → ℂ`. Assume

- `s ↦ f s x` is complex differentiable on `W` for every `x ∈ X`, and
- `(s, x) ↦ f s x` is continuous on `(W \ {s₀}) × X`.

Then there is `ρ > 0` with `ball s₀ ρ ⊆ W` such that `(s, x) ↦ f s x` is continuous on
`ball s₀ ρ × X`.

No local compactness or countability of `X` is assumed.

## Implemented proof

Choose `R > 0` with `closedBall s₀ R ⊆ W` and put `ρ = R / 2`. For `s ∈ ball s₀ ρ` and `x ∈ X`
the Cauchy integral formula (Mathlib's `DifferentiableOn.circleIntegral_sub_inv_smul`, applied to
`f · x` on `closedBall s₀ R`) gives

  `f s x = (2πi)⁻¹ ∫₀^{2π} (circleMap s₀ R)'(θ) · (circleMap s₀ R θ - s)⁻¹ · f (circleMap s₀ R θ) x dθ`.

On the subspace `ball s₀ ρ × X`, the integrand is jointly continuous in `((s, x), θ)`:

- the points `circleMap s₀ R θ` lie on the sphere of radius `R`, inside `W \ {s₀}`, so
  `(θ, x) ↦ f (circleMap s₀ R θ) x` is continuous by the second hypothesis;
- `circleMap s₀ R θ - s` does not vanish, because `|s - s₀| < ρ < R`.

Mathlib's `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` (continuity of
an integral over a fixed interval with a jointly continuous integrand and an arbitrary topological
parameter space) gives continuity of the integral on the subspace. `continuousOn_iff_continuous_domRestrict`
turns this into continuity of `f` on `ball s₀ ρ × X`.

## Use

`Langlands.Global.EisensteinLine.exists_lineContinuation` (module
`Langlands.Global.AdelicEisensteinLineContinuation`) applies the lemma with `X = G(𝔸)` at points
`s₀` where a continued Eisenstein series is holomorphic. There it is known to be jointly continuous
only off `s₀`, as the quotient of a jointly continuous function by a power of `s - s₀`. This is the
one-variable Cauchy-formula step for the imaginary axis in the reduction of
`CuspidalPairEisensteinJointContinuationStatement`.

## Provenance

This is a derived lemma: the Cauchy integral formula for a disc, applied for each parameter `x`,
together with the continuity of integrals of jointly continuous integrands over a compact
interval. Both facts are taken from Mathlib, as named above; no other source is used.
