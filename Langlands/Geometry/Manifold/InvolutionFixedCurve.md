# Smooth curves of fixed points of a smooth involution

Module `Langlands.Geometry.Manifold.InvolutionFixedCurve` (namespace
`Langlands.Geometry.Manifold.InvolutionFixedCurve`). Internal supporting result for the adapted
Casimir element (Harish-Chandra, *Two theorems on semi-simple Lie groups*, 1966, proof of
Lemma 33): directions fixed by the differential of a Cartan involution are tangent to the fixed
subgroup. The statement and proof are generic manifold calculus; no Lie group structure is used.

## Main result

`exists_contMDiff_curve_fixed`. Let `E` be a real Banach space and `M` a `C^∞` manifold modelled
on `E` with the model `𝓘(ℝ, E)` (so it has no boundary). Let `θ : M → M` be `C^∞` with
`θ (θ x) = x` for all `x`, let `p` be a fixed point of `θ`, and let `X : E` satisfy
`mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) θ p X = X`. Then there is a curve `c : ℝ → M` that is `C^∞`
(`ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ c`), with `c 0 = p`, `θ (c t) = c t` for every real `t`, and
`mfderiv 𝓘(ℝ) 𝓘(ℝ, E) c 0 1 = X`.

## Auxiliary declarations

- `bumpParam δ t = t / (1 + (t / δ)^2)`: a `C^∞` function on `ℝ` (`contDiff_bumpParam`) with
  `bumpParam δ 0 = 0`, derivative `1` at `0` (`hasDerivAt_bumpParam`), and
  `|bumpParam δ t| ≤ δ / 2` for `δ > 0` (`abs_bumpParam_le`, from `(|t| - δ)^2 ≥ 0`). It turns a
  curve defined on a small ball into one defined on all of `ℝ`.

## Proof

1. Let `ψ = extChartAt 𝓘(ℝ, E) p` and `y₀ = ψ p`. On the open set
   `T0 = ψ.target ∩ ψ.symm⁻¹ (ψ.source ∩ θ⁻¹ ψ.source)` the map `σ y = ψ (θ (ψ.symm y))` is
   `C^∞` (`contMDiffOn_iff_of_subset_source'`), `σ y₀ = y₀`, and on the smaller open set
   `T1 = T0 ∩ σ⁻¹ T0` we have `σ (σ y) = y`.
2. Let `A = fderiv σ y₀`. The chain rule applied to `σ ∘ σ`, which agrees with the identity near
   `y₀`, gives `A ∘ A = id`. Since `mfderiv θ p` is the derivative of `σ` at `y₀`
   (`MDifferentiableAt.mfderiv_abuse`, using `θ p = p`), the hypothesis gives `A X = X`.
3. Put `h y = y₀ + ½ ((y - y₀) + A (σ y - y₀))`. It is `C^∞` on `T0`, `h y₀ = y₀`, its strict
   derivative at `y₀` is `½ (id + A ∘ A) = id`, and for `y ∈ T1`,
   `h (σ y) = y₀ + A (h y - y₀)` (expand and use `A (A v) = v`).
4. The inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`) gives an open
   partial homeomorphism `Φ` with underlying map `h` and `y₀` in its source. The set `T2` of
   points of `T0` where `fderiv h` is a continuous linear equivalence is open
   (`ContinuousLinearEquiv.isOpen` and continuity of `fderiv h`) and contains `y₀`. Let `W` be the
   open set of points of `Φ.source ∩ T1 ∩ T2` whose `σ`-image lies in `Φ.source`, and choose a
   ball of radius `ρ` around `y₀` inside `Φ.target ∩ Φ.symm⁻¹ W`.
5. With `δ = ρ / (‖X‖ + 1)`, the curve `u t = y₀ + bumpParam δ t • X` stays in that ball. Put
   `γ = Φ.symm ∘ u`. At every `u t` the inverse `Φ.symm` is `C^∞`
   (`OpenPartialHomeomorph.contDiffAt_symm`, the derivative of `h` at `Φ.symm (u t)` being
   invertible because that point is in `T2`), so `γ` is `C^∞` on `ℝ`; `γ 0 = y₀`, and
   `γ'(0) = X` because `Φ.symm` has derivative the identity at `y₀`
   (`OpenPartialHomeomorph.hasFDerivAt_symm`).
6. The curve is `c = ψ.symm ∘ γ`; it is `C^∞` because `γ` takes values in the chart target, and
   `c 0 = p`. For each `t`, `y = γ t` satisfies `h y = u t` and, by step 3 and `A X = X`,
   `h (σ y) = y₀ + bumpParam δ t • A X = u t`; since `y` and `σ y` lie in `Φ.source`, where `h` is
   injective, `σ y = y`. Applying `ψ.symm` gives `θ (c t) = c t`.
7. In charts, `c` is written as `ψ ∘ ψ.symm ∘ γ = γ` (the chart of `ℝ` at `0` is the identity),
   so `mfderiv c 0 1 = γ'(0) = X`.
