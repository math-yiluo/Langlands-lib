# The Baire step of Hartogs' theorem

Module `Langlands.Analysis.SeveralComplex.Hartogs.BaireStep`, namespace
`Langlands.Analysis.SeveralComplex`. This module proves Hartogs' theorem on separately
holomorphic functions for products `B × D` with `B` open in a finite-dimensional space and
`D ⊆ ℂ` open. The induction on the dimension in `Langlands.Analysis.SeveralComplex.Hartogs.Basic`
builds on it. The proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement` needs
the result.

## Provenance

This is internal infrastructure, not a result quoted from a particular source. It follows the
classical proof of Hartogs' theorem (F. Hartogs, *Zur Theorie der analytischen Funktionen
mehrerer unabhängiger Veränderlichen*, Math. Ann. 62 (1906); see also L. Hörmander, *An
Introduction to Complex Analysis in Several Variables*, Chapter II). That proof combines the
Baire category theorem, Osgood's lemma and the extension step. Here it is stated and proved, as
below, for `B × D` with `B` an open subset of an arbitrary finite-dimensional complex normed
space `E₁`.

## Statements

Throughout, `E₁` is a finite-dimensional complex normed space.

* `exists_ball_forall_norm_le` (**Baire step**): let `0 < t` and `f : E₁ × ℂ → ℂ`. Suppose
  `z ↦ f (z, w)` is continuous on `closedBall z₀ ρ` for every `w ∈ ball w₀ t`, and
  `w ↦ f (z, w)` is continuous on `ball w₀ t` for every `z ∈ closedBall z₀ ρ`. Then there are
  `w' ∈ ball w₀ t`, `ε > 0` and `N : ℝ` with `ball w' ε ⊆ ball w₀ t` and `‖f (z, w)‖ ≤ N` for
  all `z ∈ closedBall z₀ ρ` and `w ∈ ball w' ε`.
* `differentiableOn_prod_complex_of_separately` (**Hartogs' theorem for `E₁ × ℂ`**): let
  `B ⊆ E₁` and `D ⊆ ℂ` be open. Suppose `f : E₁ × ℂ → ℂ` is holomorphic (`DifferentiableOn ℂ`)
  in `z` on `B` for each `w ∈ D`, and holomorphic in `w` on `D` for each `z ∈ B`. Then `f` is
  holomorphic on `B ×ˢ D`.

## Proofs

* `exists_ball_forall_norm_le`: for `N : ℕ` let `Z N` be the set of `w ∈ ℂ` such that
  `w ∈ ball w₀ t` implies `‖f (z, w)‖ ≤ N` for all `z ∈ closedBall z₀ ρ`. Each `Z N` is
  closed. Suppose `w` is not in `Z N`. Then `w ∈ ball w₀ t` and `N < ‖f (z, w)‖` for some `z`.
  By continuity in `w`, this persists on a neighbourhood of `w` inside `ball w₀ t`. The sets
  `Z N` cover `ℂ`. Indeed, for `w ∈ ball w₀ t`, the function `z ↦ f (z, w)` is continuous on
  the compact set `closedBall z₀ ρ`, so it is bounded there; and `Z N` contains every `w`
  outside `ball w₀ t`. By the Baire category theorem (`dense_iUnion_interior_of_closed`), the
  union of the interiors of the `Z N` is dense. So it contains a point `w'` of `ball w₀ t`, and
  some ball `ball w' ε` lies in `interior (Z N) ∩ ball w₀ t`.
* `differentiableOn_prod_complex_of_separately`: fix `(z₀, w₀) ∈ B × D`. Choose `ρ > 0` with
  `closedBall z₀ ρ ⊆ B`, and `u > 0` with `ball w₀ u ⊆ D`. Put `t = u / 3`. The Baire step
  gives `w' ∈ ball w₀ t` and a ball `ball w' ε ⊆ ball w₀ t` on which `f` is bounded for
  `z ∈ closedBall z₀ ρ`. By Osgood's lemma (`differentiableOn_prod_of_locallyBounded`, module
  `Hartogs.Osgood`), `f` is holomorphic on `ball z₀ ρ × ball w' ε`. Since
  `ball w' (2t) ⊆ ball w₀ u ⊆ D`, the extension step `differentiableOn_prod_ball_of_small`
  (module `Hartogs.TaylorCoefficients`) makes `f` holomorphic on `ball z₀ ρ × ball w' (2t)`.
  This open set contains `(z₀, w₀)`, because `‖w₀ - w'‖ < t`. So `f` is differentiable at
  `(z₀, w₀)`.
