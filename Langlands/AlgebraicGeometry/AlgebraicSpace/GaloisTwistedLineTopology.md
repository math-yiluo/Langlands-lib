# The image of `X(K)` in `X_{K'}(K')` is not closed

Author: Worker 105.

This module proves clause (3) of Conrad's Example 5.13 (printed p.20) for the Galois-twisted
line: `not_isClosed_range`. It assumes nontrivially normed fields `K` and `K'`,
`NormedAlgebra K K'`, `QuadraticConj K K'` data and `[Module.Finite K K']`.

## Setup

- `affineRingPointEquiv_ringTestMap'` evaluates `affineRingPointEquiv` on `ringTestMap` for an
  arbitrary algebra. The Library version is stated only for polynomial rings over the base.
- `linePoint K s` is `linePt K s`, viewed as a point of the affine scheme `Spec K'[X]` over `K`.
- `continuous_linePoint`: the map `s ↦ linePoint K s` is continuous for the scheme-point
  topology. Through `spectrumAlgebraPointHomeomorph` this reduces to continuity of polynomial
  evaluation.

## Proof of `not_isClosed_range`

1. Base change the atlas to `Spec K'` (`HenselianIntegralPointsNotClosed.baseChangeChart`). This
   gives an étale chart of finite type of `X_{K'}`. Its point map is continuous for the
   étale-chart topology (`EtaleFiniteTypeChart.continuous_pointMap`). Combined with the
   base-change homeomorphism (`schemeBaseChangeTopology_proof`), the map
   `Φ : K' → X_{K'}(K')`, `s ↦ a(u_s)`, is continuous.
2. `Φ s` corresponds to `a(u_s) ∈ X(K')` under `baseChangeRingPointsEquiv`
   (`baseChangeRingPointsEquiv_baseChangeChart_pointMap`).
3. `Φ 0` is not in the image of `X(K)`, by `changeRing_ne_zero`.
4. For `c ∈ K` nonzero, `Φ c` is in the image, by `exists_changeRing_eq`.
5. Choose `p₀ ∈ K` with `0 < ‖p₀‖ < 1`. Then `p₀ⁿ → 0` in `K`, hence in `K'`, and `Φ (p₀ⁿ) → Φ 0`.
   A closed image would contain `Φ 0`, which is a contradiction.

## Relation to Conrad's argument

Conrad identifies `X_{k'}` with the line with doubled origin, and `X(k) → X(k')` with the
inclusion of `k^×`. The implemented proof uses only the consequence needed for non-closedness:
points of `k^×` converge to an origin that does not come from `X(k)`.
