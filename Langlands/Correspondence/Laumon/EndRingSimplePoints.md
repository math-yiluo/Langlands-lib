# Simple points of the end ring

Module `Langlands.Correspondence.Laumon.EndRingSimplePoints`. Throughout, `ι` is the chart
coordinate `endChartCoordinate k .zero : k[x] → endRing k` (`x ↦ t`) and `t` is
`endUniformizer k .zero`.

## Definition

`IsSimplePoint k b` says that `b ∈ endRing k` is a root of a polynomial `G ∈ k[x][Y]` (evaluated
through `ι`) whose derivative `G'(b)` is a unit of `endRing k`. Geometrically, `(0, b(0))` is a
point of the plane curve `G = 0` at which `G` is smooth in the `Y`-direction, and `b` is the
branch of the curve through it. This is an internal notion: it is the input that the stage rings
of `Langlands.Correspondence.Laumon.EndRingStages` need.

## Auxiliary facts

- `endResidue_endUniformizer`, `endResidue_endChartCoordinate`, `isUnit_iff_endResidue_ne_zero`,
  `endUniformizer_ne_zero`: the residue of `t` is `0`, that of `ι a` is `a(0)`, units are the
  elements with nonzero residue, and `t ≠ 0`.
- `subtype_comp_endChartCoordinate`, `coe_endChartCoordinate`, `coe_endUniformizer`,
  `coe_eval₂_endChartCoordinate`: inside `endField k`, `ι` is the expansion
  `k[x] → k(x) → endField k`, and `p(b)` for `p ∈ k[x][Y]` is the evaluation at `b` of the image of
  `p` over `k(t)`.
- `X_pow_dvd_of_endChartCoordinate_eq`: if `ι a = t ^ n r` with `r ∈ endRing k`, then `x ^ n ∣ a`
  in `k[x]` (compare coefficients in `k⟦t⟧`).
- `exists_pow_mul_mem_endRing`: every element of `endField k` times a suitable power of `t` lies
  in `endRing k` (using `LaurentSeries.powerSeriesPart`).
- `isSimplePoint_of_eq`: if `ι u₀ = -(v b + t K₀(b) b²)` and `ι u₁ = v` with `v` a unit, then `b`
  is a simple point, with `G = u₀ + u₁ Y + x K₀ Y²`.

## The Newton shift

`exists_isSimplePoint`: every `γ ∈ endRing k` separable over `k(t)` lies in `k(t)(b)` for some
simple point `b`. The proof:

1. Clearing the denominators of the minimal polynomial of `γ` over `k(t)`
   (`IsLocalization.integerNormalization`) gives `m ∈ k[x][Y]` with `m(γ) = 0` and `m'(γ) ≠ 0`;
   write `m'(γ) = t ^ δ v` with `v` a unit (`exists_eq_endUniformizer_pow_mul`).
2. Let `N = δ + 1` and `γ_N ∈ k[x]` the truncation of the power series of `γ` below degree `N`.
   Then `γ - γ_N = t ^ N b` with `b ∈ endRing k`, and `γ = γ_N + t ^ N b ∈ k(t)(b)`.
3. Mathlib's `Polynomial.binomExpansion` in `k[x][Y]` gives
   `m(γ_N + x ^ N Y) = m(γ_N) + m'(γ_N) x ^ N Y + K₀ x ^ (2N) Y²`; evaluating at `b` gives `0`.
4. `m'(γ_N) ≡ m'(γ) (mod t ^ N)`, so `ι(m'(γ_N)) = t ^ δ v'` with `v' = v - t b c` a unit; hence
   `m'(γ_N) = x ^ δ u₁` with `ι u₁ = v'`. The vanishing at `b` then gives
   `ι(m(γ_N)) = t ^ (N + δ) · (-(v' b + t K₀(b) b²))`, hence `m(γ_N) = x ^ (N + δ) u₀`.
5. Cancelling `t ^ (N + δ)` in `endRing k` gives `ι u₀ = -(v' b + t K₀(b) b²)`, so `b` is a root
   of `G = u₀ + u₁ Y + x K₀ Y²`, and `G'(b) = v' + t (⋯)` is a unit (`isSimplePoint_of_eq`).

Provenance: internal; this is Newton's method for a branch of a plane curve through a simple
point, applied to the curve of the minimal polynomial of `γ`.
