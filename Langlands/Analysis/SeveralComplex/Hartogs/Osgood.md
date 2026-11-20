# Osgood's lemma

Module `Langlands.Analysis.SeveralComplex.Hartogs.Osgood`, namespace
`Langlands.Analysis.SeveralComplex`. This module is the first step towards Hartogs' theorem on
separate holomorphy, which the proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement` needs (Task 5431).

## Provenance

This is internal infrastructure, not a result quoted from a particular source. Osgood's lemma is
classical: a locally bounded function that is holomorphic in each variable separately is
holomorphic (W. F. Osgood, *Note über analytische Functionen mehrerer Veränderlichen*, Math. Ann.
52 (1899); see also L. Hörmander, *An Introduction to Complex Analysis in Several Variables*,
Chapter II). The usual textbook proof goes through Cauchy's integral formula on polydiscs. The Lean
proof below uses a first-order argument with the Schwarz lemma instead. It works for arbitrary
complex normed spaces `E₁`, `E₂`, with no finite-dimensionality or completeness assumption.

## Statements

Throughout, `E₁` and `E₂` are complex normed spaces.

* `norm_sub_le_of_forall_norm_le`: if `h : E₁ → ℂ` is holomorphic on `ball x₀ r` and bounded
  by `B` there, then `‖h x - h x₀‖ ≤ 2 B / r · ‖x - x₀‖` for `x ∈ ball x₀ r`.
* `hasFDerivAt_of_forall_norm_le`: let `0 < r`, and let `f : E₁ × E₂ → ℂ` be bounded by `B` on
  `ball x₀ r × ball y₀ r` and holomorphic in each variable separately there. Then `f` has, at
  `(x₀, y₀)`, the Fréchet derivative `D₁ ∘ fst + D₂ ∘ snd`, where `D₁` and `D₂` are the
  derivatives of `x ↦ f (x, y₀)` at `x₀` and of `y ↦ f (x₀, y)` at `y₀`.
* `differentiableOn_prod_of_locallyBounded` (**Osgood's lemma**): let `U ⊆ E₁` and `V ⊆ E₂` be
  open, and let `f : E₁ × E₂ → ℂ` be holomorphic in `x ∈ U` for each `y ∈ V` and in `y ∈ V`
  for each `x ∈ U`. Suppose every point of `U × V` has a neighbourhood on which `‖f‖` is bounded.
  Then `f` is holomorphic (`DifferentiableOn ℂ`) on `U × V`.

## Proofs

* `norm_sub_le_of_forall_norm_le`: `h` maps `ball x₀ r` into `closedBall (h x₀) (2B)`.
  Mathlib's Schwarz-lemma estimate `Complex.dist_le_div_mul_dist_of_mapsTo_ball` gives the
  bound.
* `hasFDerivAt_of_forall_norm_le`: write the increment `f (x₀ + a, y₀ + b) - f (x₀, y₀)` as the
  mixed second difference plus the two one-variable increments. The one-variable increments
  differ from `D₁ a` and `D₂ b` by `o(‖(a, b)‖)`. For the mixed second difference, put
  `g y = f (x₀ + a, y) - f (x₀, y)`. The first bullet, applied in the first variable, bounds
  `‖g‖` by `2B/r · ‖a‖` on `ball y₀ r`. Applying it once more to `g` bounds the second
  difference by `4B/r² · ‖a‖ ‖b‖ ≤ 4B/r² · ‖(a, b)‖²`, which is `o(‖(a, b)‖)`.
* `differentiableOn_prod_of_locallyBounded`: around a point `(x₀, y₀) ∈ U × V` choose `r > 0`
  such that `ball x₀ r × ball y₀ r` lies in `U × V` and in the set where `‖f‖ ≤ B`. Then
  apply the previous bullet.
