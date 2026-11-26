# A compatible quotient measure near the identity coset

The module `Langlands.Analysis.Local.WeylChartQuotient` computes a compatible quotient
measure on `LeftQuotient (torusGroup γ)` near the identity coset in the transverse coordinate
`cosetChart`. Here `F` and `R` are as in `Langlands.Analysis.Local.WeylChartTorus`, `γ` is in
regular position, `r` is a small radius, and the product map is a bijection from the closed
coordinate ball of radius `r` onto `coordCLE` of that ball and pushes the restricted
coordinate Haar measure to the restricted image measure, as
`exists_productMap_pushforward` provides for small `r`.

## Coset sets

For a set `U` of transverse vectors, `cosetSet γ r U` is the set of inverses
`(unitOf (1 + y) * unitOf (1 + s))⁻¹` with `y ∈ U` and `‖s‖ ≤ r`. When `U` lies in the ball:

- it lies in `unitBall` (`cosetSet_subset_unitBall`), and for `k ∈ unitBall`,
  `k ∈ cosetSet γ r U` exactly when the coset of `k` lies in `cosetChart '' U`
  (`mem_cosetSet_iff`, `mem_cosetSet_iff'`), by `leftQuotientMap_eq_cosetChart`;
- `cosetChart '' U` is the image of `cosetSet γ r U` in the quotient
  (`image_cosetChart_eq`);
- if `U` is open (compact), then `cosetSet γ r U` and `cosetChart '' U` are open (compact)
  (`isOpen_cosetSet`, `isCompact_cosetSet`, `isOpen_image_cosetChart`,
  `isCompact_image_cosetChart`).

## The Weil formula on coset sets

- `quotientAverage_indicator_cosetSet`: the torus average of the indicator of
  `cosetSet γ r U` is `μT (torusBall)` times the indicator of `cosetChart '' U`. If the coset
  of `g` is `cosetChart y` with `y ∈ U`, write `g = t₀ g₀` with `g₀ = unitOf (1 + y)⁻¹` and
  `t₀` in the torus; the torus elements `h` with `h g` in the coset set are those with
  `h t₀ ∈ torusBall`, a set of measure `μT (torusBall)` by right invariance. On any other
  coset there are none.
- `torusBall_mul_measure_image_cosetChart`: for `U` open and compact and `ν` compatible with
  Haar measures `μ` on `Rˣ` and `μT` on the torus (`IsCompatible`),
  `μT (torusBall) * ν (cosetChart '' U) = μ (cosetSet γ r U)`. The indicator of the compact
  open set `cosetSet γ r U` is continuous with compact support, so the integral formula of
  `IsCompatible` applies to it.

## Haar measure of coset sets

- `ringHaar_image_productMap`: for compact `S` in the coordinate ball,
  `ringHaar (productMap '' S) = coordHaar S`, evaluating the pushforward identity on the
  image of `S`.
- `measure_cosetSet`: for right invariant `μ` and compact `U` in the ball,
  `μ (cosetSet γ r U) = identityConst μ * coordHaar (U ×ˢ closedBall 0 r)`. Right
  invariance makes `μ` inversion invariant, which replaces the coset set by the image of
  `U ×ˢ closedBall 0 r` under `unitMap`. Its value set is a translate by `1` of the
  product-map image, and `map_val_restrict_of_subset_unitBall` with translation invariance of
  `ringHaar` gives the value.
- `measure_image_cosetChart`: for `U` open and compact in the ball,
  `ν (cosetChart '' U) = cosetConst * addHaar U`, where
  `cosetConst = identityConst μ * addHaar (closedBall 0 r) * (μT (torusBall))⁻¹`. Divide the
  previous two identities by the positive finite number `μT (torusBall)`.

## The local form of the quotient measure

`measurable_cosetChart` and `continuousOn_cosetChart` record the regularity of the coset
chart. The main result is `restrict_image_cosetChart`:

`ν.restrict (cosetChart '' B) = cosetConst • ((addHaar).restrict B).map cosetChart`,

with `B` the transverse closed ball of radius `r`. On the compact ball, `cosetChart` is a
continuous injection (`cosetChart_injOn`), hence a closed measurable embedding. The pullback
of `ν` along it is finite and, by `measure_image_cosetChart`, agrees with `cosetConst` times
additive Haar measure on every closed sub-ball and on the whole ball. Every closed ball of
positive radius about a point of `B` meets `B` in a closed ball contained in `B`, because
in an ultrametric space every point of a ball is its center. `measure_ext_of_closedBall`
then identifies the two measures, and pushing forward gives the identity.
