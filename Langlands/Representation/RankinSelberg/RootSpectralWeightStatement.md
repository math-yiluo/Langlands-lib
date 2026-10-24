# Spectral determinant weight in root coordinates

`Langlands.RankinSelberg.RootSpectralWeightStatement F T n` is an internal
proposition target for every specified p-adic field, supplied topological data
`T`, and natural number `n`. It uses rank `n + 1`, including rank one.

Let `K` be the actual integral general linear subgroup determined by the
valuation from `T`. The first assertion is that every element of `K` has
`T.normalizedAbs` of its determinant equal to one.

For a unit tuple `a`, set `d(a)_i = ∏_{j ≥ i} a_j`. For any invertible matrix
`k` with normalized determinant absolute value one and every complex `s`, put
`g = diagonalUnits(d(a)) * k`. The remaining assertions are

```text
determinantWeight (normalizedAbsoluteValue T) g s
  = ∏ i, (T.normalizedAbs(a_i) : ℂ)^((i + 1) * s),

‖determinantWeight (normalizedAbsoluteValue T) g s‖
  = ∏ i, T.normalizedAbs(a_i)^((i + 1) * Re(s)).
```

The first powers are complex powers; the second are real powers. Indices run
from zero through `n`. The determinant condition is explicit, so the formulas
apply in particular to the integral subgroup and also to any other matrix
satisfying that condition. No restriction on `s` is imposed.

This is an internal adapter, with no independent literature attribution.
Its provenance is the determinant identity in `RootCoordinateChangeStatement`,
the determinant-valuation identity for `Conductor.integralSubgroup`, the
published residue-cardinality normalization of `T.normalizedAbs`, and the
positive-real complex-power identities in Mathlib. The unit coordinates have
strictly positive normalized absolute values, which makes the product and
power identities compatible with the principal complex power. The proposition
does not assert convergence, a measure identity, or rational continuation.
