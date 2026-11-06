# Local Haar-measure estimates for nearly linear maps

Module `Langlands.Global.LocalModularCharacter.LocalScaling`.

This module holds the local analysis on a chart. `E` is a normed additive group with its Borel
σ-algebra and an additive Haar measure `μ`; in applications `E = K^d` for a completion `K` of a
number field. The module gives two kinds of estimate on small balls around `0`:

- (P1) near-translation families `z ↦ m y z` increase the measure of subsets of a small ball
  by at most a factor `1 + η`;
- (P2) a map `ψ` with `ψ 0 = 0` and derivative `A` at `0` sends a small ball `B` to a set of
  measure at most `(1 + η) · addEquivAddHaarChar e · μ B`, where `e` is `A` viewed as a
  continuous additive automorphism.

Both estimates are proved in the archimedean case (`E` a finite-dimensional real normed space)
and in the ultrametric case (`IsUltrametricDist E`). These are the inputs that the comparison
skeleton `ComparisonMeasure` needs from a chart. The module does not mention group schemes.

## General lemmas

- `measure_image_eq_addEquivAddHaarChar_mul`: `μ (e '' Y) = addEquivAddHaarChar e * μ Y` for
  a continuous additive automorphism `e` and any set `Y`. It restates Mathlib's
  `addEquivAddHaarChar_smul_preimage` with `X = e '' Y`.
- `near_translation_estimate`: let `m : E → E → E` be a two-variable map such that
  `p ↦ m p.1 p.2` has strict derivative `L` at `(0, 0)` and `L (0, w) = w`. Then for every
  `δ > 0` there is `r > 0` with
  `‖m y z - m y z' - (z - z')‖ ≤ δ ‖z - z'‖` for all `y, z, z'` in the open ball of radius `r`.
  This is the strict-derivative little-o bound applied at the pair of points `(y, z)` and
  `(y, z')`, whose difference is `(0, z - z')`.
- `image_ball_subset_of_hasFDerivAt`: if `ψ 0 = 0`, `ψ` has derivative `A` at `0` (with `A` a
  continuous linear automorphism over a nontrivially normed field) and `ε > 0`, then there is
  `r₀ > 0` with `ψ '' ball 0 r ⊆ A '' ball 0 ((1 + ε) r)` for all `r ≤ r₀`. For `z` in the ball,
  write `ψ z = A (z + u)` with `u = A⁻¹ (ψ z - A z)`; the derivative bound with constant
  `ε / (‖A⁻¹‖ + 1)` gives `‖u‖ ≤ ε ‖z‖`.

## Archimedean case

Assumptions: `E` is a finite-dimensional real normed space (`[NormedSpace ℝ E]`,
`[FiniteDimensional ℝ E]`).

- `measure_image_le_of_near_translation` (P1): given the uniform near-translation bound of
  `near_translation_estimate` for a family `m`, for every `η > 0` there is `r > 0` with
  `μ (m y '' X) ≤ (1 + η) μ X` for all `y` in the ball of radius `r` and all `X` inside that
  ball. Proof: Mathlib's `addHaar_image_le_mul_of_det_lt` for the identity map (determinant `1`)
  gives `δ > 0` such that every map that approximates the identity on `X` with constant `δ`
  increases the measure of `X` by at most `1 + η`. The near-translation bound with this `δ`
  says exactly that `m y` approximates the identity on the ball.
- `measure_image_ball_le_of_hasFDerivAt` (P2): with `ψ`, `A` as above, `e` a continuous additive
  automorphism with the same underlying function as `A`, and `η > 0`, there is `r₀ > 0` with
  `μ (ψ '' ball 0 r) ≤ (1 + η) · addEquivAddHaarChar e · μ (ball 0 r)` for all `r ≤ r₀`.
  The scalar field of `A` is an arbitrary nontrivially normed field acting on `E`. Proof:
  choose `ε > 0` with `(1 + ε)^n < 1 + η`, where `n = finrank ℝ E`. Then
  `ψ '' ball 0 r ⊆ A '' ball 0 ((1 + ε) r)`, the image under `A` scales measure by
  `addEquivAddHaarChar e`, and `μ (ball 0 ((1 + ε) r)) = (1 + ε)^n μ (ball 0 r)`
  (`addHaar_ball_mul_of_pos`).

## Ultrametric case

Assumptions: `IsUltrametricDist E`, and from the determinant estimate on, `ProperSpace E`.

- `image_ball_subset_of_hasFDerivAt_ultrametric`: there is `r₀ > 0` with
  `ψ '' ball 0 r ⊆ A '' ball 0 r` for all `r ≤ r₀`. The same decomposition `ψ z = A (z + u)` now
  gives `‖u‖ ≤ ‖z‖`, hence `‖z + u‖ ≤ max ‖z‖ ‖u‖ < r`.
- `measure_image_ball_le_of_hasFDerivAt_ultrametric` (P2): the same conclusion as the
  archimedean P2, for every `η ≥ 0`. It follows directly from the containment above.
- `isPiSystem_closedBalls`: in an ultrametric space two closed balls are disjoint or nested,
  so closed balls form a π-system.
- `measurableSpace_eq_generateFrom_closedBalls`: if `E` is also second countable, closed balls
  generate the Borel σ-algebra. Closed balls of positive radius are open in an ultrametric
  space and form a topological basis.
- `measurable_piecewise_closedBall`: a map that is isometric on a closed ball `B`, extended by
  the identity outside `B`, is measurable.
- `map_piecewise_restrict_closedBall`: let `h` map the closed ball `B` onto itself
  isometrically. Then `h` extended by the identity pushes `μ.restrict B` to itself. Proof:
  both measures are finite, so it suffices to compare them on closed balls
  (`ext_of_generate_finite`). Take a closed ball `B'` of radius `r` that meets `B`, which has
  radius `ρ`. If `ρ ≤ r` then `B ⊆ B'` and both sides equal `μ B`. Otherwise `B' ⊆ B`; write
  the center of `B'` as `h z₀`. The preimage of `B'` in `B` is the closed ball of radius `r`
  around `z₀`, and closed balls with the same radius have the same measure.
- `measure_image_le_of_isometry_closedBall` (the ultrametric P1 tool): let `f` map a closed
  ball `B` isometrically into itself, with an inverse `h` on `B` that also maps `B` into
  itself. Then `μ (f '' X) ≤ μ X` for every `X ⊆ B`. Proof: `f '' X` lies in the preimage of a
  measurable hull of `X` under the extension of `h`, and that extension preserves
  `μ.restrict B`.
- `dist_eq_of_near_translation`: if `‖f z - f z' - (z - z')‖ ≤ ‖z - z'‖ / 2`, then
  `dist (f z) (f z') = dist z z'`. All triangles in an ultrametric group are isosceles
  (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`).
- `measure_image_le_of_near_translation_ultrametric` (ultrametric P1): let `m : E → E → E` and
  `ι : E → E` satisfy
  - the near-translation estimate of `near_translation_estimate`, for every `δ > 0` on a
    ball of some radius `r > 0`;
  - `m y 0 = y` for `y` near `0`;
  - `ι y → 0` as `y → 0`;
  - `m (ι y) (m y z) = z` and `m y (m (ι y) z) = z` for `(y, z)` near `(0, 0)`.

  Then there is `r > 0` with `μ (m y '' X) ≤ μ X` for all `y ∈ ball 0 r` and `X ⊆ ball 0 r`.
  Here `m y z` is the group law read in a chart, and `ι y` is the chart point of the inverse.
  Proof: take `δ = 1/2` and a radius `s` so small that all hypotheses hold on a larger ball
  and `ι` maps `ball 0 s` into it. For `‖w‖ ≤ s`, the map `m w` is isometric on
  `B = closedBall 0 s` by the previous lemma, and maps `B` into `B`, because
  `m w z = (m w z - w - z) + w + z` is a sum of three terms of norm at most `s`. For
  `‖y‖ < s`, `m (ι y) y = m (ι y) (m y 0) = 0` and `m (ι y) 0 = ι y`. The estimate for the
  pair `(y, 0)` then gives `‖-ι y - y‖ ≤ ‖y‖ / 2`, hence `‖ι y‖ ≤ ‖y‖ ≤ s`. Apply
  `measure_image_le_of_isometry_closedBall` with `f = m y` and `h = m (ι y)`.

## Provenance

These are standard facts of real analysis and of analysis over ultrametric fields, written for
this project as internal steps toward the Library statement
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. The module
cites no literature statement. The archimedean estimates use Mathlib's change-of-variables bound
`addHaar_image_le_mul_of_det_lt`. The ultrametric Haar-preservation lemma is proved here
directly from the π-system of closed balls.
