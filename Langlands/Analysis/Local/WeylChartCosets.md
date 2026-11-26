# Cosets of the torus near the identity

The module `Langlands.Analysis.Local.WeylChartCosets` collects the facts about cosets of the
torus `torusGroup γ` near the identity coset that the quotient measure computation needs.

## A uniqueness criterion for measures

`measure_ext_of_closedBall`: on a second countable ultrametric metric space with its Borel
structure, a finite measure `μ` and a measure `ν` that agree on every closed ball of positive
radius and on the whole space are equal. In an ultrametric space two closed balls are
disjoint or one contains the other (`IsUltrametricDist.closedBall_subset_trichotomy`), so
closed balls of positive radius form a π-system. They are open and form a basis of the
topology, so by second countability they generate the Borel σ-algebra. Mathlib's
`ext_of_generate_finite` concludes.

## Coordinates of cosets

In the rest of the module `F` and `R` are as in `Langlands.Analysis.Local.WeylChartTorus`,
`γ` is in regular position, `r` is a small radius and the product map is a bijection from the
closed ball of radius `r` onto `coordCLE` of that ball.

- `unitOf_one`: `unitOf 1 = 1`.
- `exists_torusUnit_eq`: every element of `torusBall` is `torusUnit γ s` for some central `s`
  with `‖s‖ ≤ r`.
- `cosetChart_injOn`: `cosetChart γ` is injective on the transverse ball of radius `r`. Let
  `u = unitOf (1 + y)` and `u' = unitOf (1 + y')` with `u⁻¹` and `u'⁻¹` in the same coset.
  Then `u'⁻¹ u` lies in the torus and in `unitBall`, hence in `torusBall`, so it is
  `unitOf (1 + s)` with `‖s‖ ≤ r`. This gives `u · unitOf (1 + 0) = u' · unitOf (1 + s)`,
  and uniqueness of the product decomposition (`eq_of_unitOf_mul_unitOf_eq`) forces
  `y = y'`.
- `leftQuotientMap_eq_cosetChart`: for `k ∈ unitBall`, write
  `k⁻¹ = unitOf (1 + y) * unitOf (1 + s)` with `‖(y, s)‖ ≤ r`; then the coset of `k` is
  `cosetChart γ y`, since `k = unitOf (1 + s)⁻¹ · unitOf (1 + y)⁻¹` and the first factor
  lies in the torus.
- `unitMap γ (y, s) = unitOf (1 + y) * unitOf (1 + s)`; it is continuous on the ball
  (`continuousOn_unitMap`) and its value is `1 + productMap γ (y, s)` there (`val_unitMap`).
- `isOpen_image_productMap`, `isOpen_image_unitMap`: the product map and the unit map send
  open subsets of the coordinate ball to open sets. On the compact ball the product map is a
  continuous injection, hence a closed embedding; its image `coordCLE '' ball` is open,
  because closed balls are open in the ultrametric coordinate space.
