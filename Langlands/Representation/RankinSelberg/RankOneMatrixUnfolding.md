# Unfolding the matrix integral over the unipotent variable

Module `Langlands.Representation.RankinSelberg.RankOneMatrixUnfolding`, namespace
`Langlands.RankinSelberg.RankOneIwasawa`. This is a helper module of the positive-rank
branch of the proof of `RankOneMatrixWhittakerComparisonStatement`. The setting is a
canonical `p`-adic field, `G = GL_(n+1)(F)`, the canonical normalized absolute value
`abv = normalizedAbsoluteValue F.canonicalTopologicalData`, and the published integrand
`GodementJacquet.matrixIntegrand abv Φ s f y = Φ(y) f(y) |det y|^s`.

## Objects

- `diagPoint F (g, (a, k)) = diag(det g / ∏ a, a) · k`.
- `outerMeasure F n = |det g|⁻ⁿ dg × (ω(1, a) da × dk|_K)`. These are the outer factors
  of `unfoldedMeasure` from `RankOneMatrixIwasawa`, and
  `unfoldedMeasure F n = outerMeasure F n × du` holds by definition (`unfoldedMeasure_eq`).
- `integralSet F n` is `GL_(n+1)(O)` as a set.

## Results

Let `f : G → ℂ` satisfy `f(u y) = θ(u) f(y)` for upper unipotent `u`, where `θ` is the
standard character.

- `matrixIntegrand_unfoldedPoint`: at `u · D(g, a) k` the integrand is
  `Φ(u D k) θ(u) · f(D k) |det D k|^s`. Here `det u = 1` (`det_unipotent_mul`).
- `integral_matrixIntegrand_unfold`: if the matrix integrand is integrable for
  `generalLinearHaar F n`, then `x ↦ J(D x) f(D x) |det D x|^s` is integrable for
  `outerMeasure F n`, and the two integrals are equal. Here
  `J = unipotentTransform F ψ Φ`. The proof transports integrability and the integral
  along `map_unfoldedMeasure` (`integrable_map_measure`, `integral_map`). It then
  integrates the unipotent variable first (`Integrable.integral_prod_left`,
  `integral_prod`) and pulls the factor independent of `u` out of the inner integral.
- `lintegral_matrixIntegrand_unfold`: for measurable `f`, the integral of
  `‖Φ f |det|^s‖ₑ` over `G` equals
  `∫⁻ x, (∫⁻ u, ‖Φ(u D x)‖ₑ du) · ‖f(D x) |det D x|^s‖ₑ` over `outerMeasure F n`. This
  uses `lintegral_map`, `lintegral_prod` and `|θ| = 1`. No integrability is assumed.
- `abv_det_eq_one` (`|det k| = 1` for integral `k`), `determinantWeight_diagPoint`
  (`|det D(g, a) k| = |det g|` for integral `k`, via `det_point`) and
  `ae_outerMeasure_mem` (almost every outer parameter has integral `k`).
- `measurable_determinantWeight` and `continuous_diagPoint` supply the measurability.

## Provenance and scope

This is the first step of the comparison in Jacquet–Piatetski-Shapiro–Shalika (1979),
Section 4: integrate the test function against the character over `N`. The formula
itself is the Iwasawa integration formula of `RankOneMatrixIwasawa`. The module assumes
no convergence. The integral form takes absolute convergence of the matrix integral as
a hypothesis, and the absolute form computes the absolute integral unconditionally.
