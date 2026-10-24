# Proof of joint continuity for bounded multiplicative spectra

Author: Worker 377.

`Langlands.Analytic.BanachSpectrum.jointContinuity` proves the entire
proposition `Langlands.Analytic.BanachSpectrum.JointContinuityStatement`
in `Spectrum.JointContinuityStatement`, for independent universes `u`,
`v` and `w`. It is the conjunction of three component theorems, and each
of those comes from a reusable lemma with explicit arguments. The proof
uses only the definitions in `Spectrum.Definitions`: a spectrum point is
a multiplicative ring seminorm bounded by the norm, and the spectrum has
the topology induced by evaluation into `A → ℝ`. It does not use
completeness, an ultrametric norm, a scalar field, a nonempty spectrum,
or a common bound for a family of ring maps.

## Uniform evaluation bound

`abs_sub_le_norm_sub x a b` proves `|x(a) - x(b)| ≤ ‖a - b‖` for every
normed commutative ring `A`, spectrum point `x`, and `a, b : A`.
Mathlib's `abs_sub_map_le_sub` applies to the underlying seminorm. It is
the reverse triangle inequality `|x(a) - x(b)| ≤ x(a - b)`. The field
`x.le_norm (a - b)` then gives `x(a - b) ≤ ‖a - b‖`. The constant is one
for every point. `uniformEvaluationBound` is this lemma stated as
`UniformEvaluationBoundStatement.{u}`.

## Joint evaluation

`continuous_eval` proves that `(x, a) ↦ x(a)` is continuous on
`BanachSpectrum A × A`. The proof checks continuity at each point
`(x₀, a₀)`. The map `(x, a) ↦ x(a₀)` is the continuous evaluation
`evaluation a₀` composed with the first projection, so it tends to
`x₀(a₀)`. By the first lemma, its distance from `x(a)` is
`|x(a₀) - x(a)| ≤ ‖a₀ - a‖`, which bounds it independently of `x`. This
bound tends to `‖a₀ - a₀‖ = 0` by continuity of the norm and of the
second projection. Mathlib's `squeeze_zero` shows that the distance
tends to zero. `Filter.Tendsto.congr_dist` then transfers the limit
`x₀(a₀)` to `x(a)`. This is the planned split of the difference through
`x(a₀)`, expressed through limits.

`Continuous.banachSpectrum_apply` is a corollary for later use. If
`x : X → BanachSpectrum A` and `a : X → A` are continuous, for any
topological space `X`, then so is `t ↦ x(t)(a(t))`. It composes
`continuous_eval` with the paired map.
`jointEvaluationContinuity` is `continuous_eval` stated as
`JointEvaluationContinuityStatement.{u}`.

## Parametric pullback

`continuous_comap_of_continuous_apply f hf` takes an arbitrary
topological space `T`, a function `f : T → BoundedRingHom A B`, and the
hypothesis that `t ↦ f(t)(a)` is continuous for each `a : A`. It proves
that `(t, x) ↦ comap (f t) x` is continuous on `T × BanachSpectrum B`.
The topology on `BanachSpectrum A` is induced from the product topology
on `A → ℝ`. By `continuous_induced_rng` and `continuous_pi`, it suffices
to prove that each coordinate `(t, x) ↦ (comap (f t) x)(a)` is
continuous. By the definition of `comap`, this coordinate is
`x(f(t)(a))`. The spectrum argument `x` is the continuous second
projection. The algebra argument `f(t)(a)` is the hypothesis `hf a`
composed with the first projection. `Continuous.banachSpectrum_apply`
proves continuity of the evaluation. The bound of each `f t` is used
only by `comap` itself, to show that the pulled-back seminorm is a
spectrum point. Continuity uses no common bound and no topology on
`BoundedRingHom A B`. `parametricPullbackContinuity` is this lemma
stated as `ParametricPullbackContinuityStatement.{u, v, w}`.

## Assembly

`jointContinuity` is the anonymous-constructor triple of the three
component theorems. It adds no premise or output hypothesis. The Lean
check reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The source context is the one documented in the target Markdown:
Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
printed/PDF p. 4, Definition 1.2.3, Exercise 1.2.4 and Definition 1.2.5,
registered as `berkovich-2009-trieste-analytic-spaces`. The three
joint-continuity targets are derived consequences rather than attributed
numbered claims. This proof is internal and follows the route proposed in
the target Markdown.
