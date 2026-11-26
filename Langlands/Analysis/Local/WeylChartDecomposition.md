# The product decomposition of the coordinate subgroup

The module `Langlands.Analysis.Local.WeylChartDecomposition` shows that, near the identity,
every unit factors uniquely as a transverse unit times a central unit. Here `F` and `R` are as
in `Langlands.Analysis.Local.WeylChartTorus`, `γ` is in regular position and `r` is a small
radius.

## Results

- `isUnit_one_add_of_norm_lt_one`: `1 + a` is a unit when `‖a‖ < 1`.
- `coordCLE_symm_transverse`, `norm_coordCLE_symm_transverse`: a transverse vector `y` has
  coordinates `(y, 0)` and coordinate norm `‖y‖`.
- `isUnit_one_add_transverse`, `isUnit_one_add_central`, `unitOf_transverse_mem`,
  `unitOf_central_mem`: for transverse `y` or central `s` of norm at most `r`, `1 + y` and
  `1 + s` are units in `unitBall hγ hr`.
- `val_unitOf_mul_unitOf`: for `‖(y, s)‖ ≤ r`, the value of
  `unitOf (1 + y) * unitOf (1 + s)` is `1 + productMap γ (y, s)`.

Assume moreover that the product map is a bijection from the closed ball of radius `r` onto
`coordCLE` of that ball, as `exists_productMap_pushforward` provides for small `r`.

- `exists_eq_unitOf_mul_unitOf`: every `k ∈ unitBall hγ hr` is
  `unitOf (1 + y) * unitOf (1 + s)` for some `(y, s)` of norm at most `r`. Indeed `k − 1`
  lies in `coordCLE` of the ball, so it is `productMap (y, s)` for such a coordinate.
- `eq_of_unitOf_mul_unitOf_eq`: the coordinate is unique, by injectivity of the product map
  on the ball.
