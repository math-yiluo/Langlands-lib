# Root lifting over fields with Henselian norm valuation ring

Author: Worker 239.

Helper module for the proof in
[HenselianSmoothOpenMapProof](HenselianSmoothOpenMapProof.md). All declarations are in the
namespace `Langlands.AlgebraicGeometry.PointTopology.HenselianRoot`. No completeness,
local compactness, discreteness or characteristic hypothesis is used. The only input from
Henselianity is Mathlib's field `HenselianLocalRing.is_henselian`: a monic polynomial with a
residually simple approximate root has a root lifting it.

## Hensel's lemma for a non-monic normalized polynomial

`exists_isRoot_of_coeff`: let `O` be a Henselian local ring and `R : O[X]` with
`R.coeff 0 = 1`, `R.coeff 1 = -1`, and `R.coeff k` in the maximal ideal for every `k ≥ 2`.
Then `R` has a root in `O`. The polynomial need not be monic.

Proof. Let `N = R.natDegree`. Then `N ≥ 1` because the linear coefficient is nonzero; write
`N = M + 1`. The reflection `Q = reflect N R` is monic, since its leading coefficient is
`R.coeff 0 = 1`. Modulo the maximal ideal, `R` reduces to `1 - X`. Since reflection commutes
with `Polynomial.map`, `Q` reduces to `X ^ (M + 1) - X ^ M`. That reduction vanishes at `1`,
and its derivative `(M + 1) - M = 1` does not. Hence `Q.eval 1` lies in the maximal ideal and
`Q.derivative.eval 1` is a unit. Henselianity gives a root `V` of `Q` with `V - 1` in the
maximal ideal, so `V` is a unit. Mathlib's `eval₂_reflect_eq_zero_iff` then shows that `V⁻¹`
is a root of `R`.

## The norm valuation ring

Let `K` be a nontrivially normed field with `IsUltrametricDist K`. Write `𝒪` for
`(NormedField.valuation (K := K)).valuationSubring`, the ring named by the published
statement (local notation only).

- `mem_valuationSubring_iff`: `x ∈ 𝒪 ↔ ‖x‖ ≤ 1`, since `NormedField.valuation x = ‖x‖₊`.
- `isUnit_valuationSubring_iff`: an element of `𝒪` is a unit iff its norm is `1`. If it has
  an inverse in `𝒪`, both norms are at most `1` and their product is `1`. Conversely, an
  element of norm `1` has a field inverse of norm `1`, which lies in `𝒪`.
- `mem_maximalIdeal_valuationSubring_iff`: an element of `𝒪` lies in the maximal ideal iff
  its norm is `< 1`. The maximal ideal is the set of nonunits.

## Roots with norm bounds

Assume moreover `HenselianLocalRing 𝒪`, the hypothesis of the published statement.

`exists_root_norm_le`: let `G : K[X]` with `c₁ = G.coeff 1 ≠ 0`, and suppose that
`‖G.coeff k‖ * ‖c₀‖ ^ (k - 1) < ‖c₁‖ ^ k` for all `k ≥ 2`, where `c₀ = G.coeff 0`. Then `G`
has a root `y` with `‖y‖ ≤ ‖c₀‖ / ‖c₁‖`.

Proof. If `c₀ = 0`, take `y = 0`. Otherwise let `e = -c₀ / c₁` and
`RK = C c₀⁻¹ * G.comp (C e * X)`. Its coefficients are `c₀⁻¹ * G.coeff k * e ^ k`, so
`RK.coeff 0 = 1`, `RK.coeff 1 = -1`, and for `k ≥ 1`

```text
‖RK.coeff k‖ = ‖G.coeff k‖ * ‖c₀‖ ^ (k - 1) / ‖c₁‖ ^ k.
```

By hypothesis this is `< 1` for `k ≥ 2`. All coefficients therefore lie in `𝒪`, so
`RK` lifts to `R : 𝒪[X]` (Mathlib's `lifts_iff_coeff_lifts`). The lift satisfies the
hypotheses of `exists_isRoot_of_coeff`, which gives a root `Z ∈ 𝒪` of `R`. Its image is a
root of `RK`. So `y = e * Z` is a root of `G`, and `‖y‖ = ‖e‖ ‖Z‖ ≤ ‖c₀‖ / ‖c₁‖`.

`eventually_exists_root`: let `T` be a topological space, `t₀ : T` and `G : T → K[X]`. Assume
every coefficient function `t ↦ (G t).coeff k` is continuous at `t₀`, and every `G t` has
`natDegree ≤ N`. If `(G t₀).coeff 0 = 0` and `(G t₀).coeff 1 ≠ 0`, then for every `ε > 0`,
eventually near `t₀` the polynomial `G t` has a root of norm `< ε`.

Proof. Near `t₀`, `(G t).coeff 1 ≠ 0`. For each of the finitely many `k ∈ [2, N]`, the
strict inequality `‖(G t).coeff k‖ * ‖(G t).coeff 0‖ ^ (k - 1) < ‖(G t).coeff 1‖ ^ k` holds
at `t₀` because the left side is `0`. It therefore holds near `t₀` by continuity
(`ContinuousAt.eventually_lt`, combined by `eventually_all_finset`). The ratio
`‖(G t).coeff 0‖ / ‖(G t).coeff 1‖` is `0` at `t₀` and continuous there, so it is
eventually `< ε`. For `k > N` the coefficient vanishes, so the inequality holds trivially.
At such `t`, `exists_root_norm_le` gives a root of norm at most the ratio, hence `< ε`.

## Provenance

This is internal infrastructure for
`HenselianSmoothRationalPointOpenMapStatement`; see the provenance section of
[HenselianSmoothOpenMapStatement](HenselianSmoothOpenMapStatement.md). The argument is a
standard Newton-polygon form of Hensel's lemma for valued fields with Henselian valuation
ring. The reduction from non-monic to monic polynomials by reflection is chosen here
because Mathlib's `HenselianLocalRing` only provides monic lifting.
