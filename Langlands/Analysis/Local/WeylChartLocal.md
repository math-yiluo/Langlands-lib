# The local pushforward of the orbit map at a regular unit

The module `Langlands.Analysis.Local.WeylChartLocal` proves the local change of variables for
the orbit map `(T x, h) ↦ x⁻¹ h x` at the base point `(T · 1, γ)`, where `T = torusGroup γ`
is commutative and `γ` is in regular position. Here `F` is a complete, proper, ultrametric
nontrivially normed field, `R` a finite-dimensional, complete, ultrametric normed `F`-algebra,
and `R`, `Rˣ` and the coset space carry Borel structures.

## Constants

- `identityConst_eq`: the density constant `identityConst hγ hr μ` of a Haar measure `μ` near
  the identity does not depend on the admissible radius. `identityConst_ne_zero` and
  `identityConst_ne_top` show it is positive and finite.
- `chartScale hγ`: the Haar scaling factor (`addHaarScalarFactor`) of the pushforward of
  `coordHaar γ` under `chartDerivative hγ`, relative to `ringHaar hγ`.
  `map_chartDerivative` records `(coordHaar γ).map chartDerivative = chartScale • ringHaar`.
  For `GL_n` this factor is the inverse absolute Weyl discriminant
  (`Langlands.BaseChange.OrdinaryWeylHaarLocalPushforwards`).

## The source measure in coordinates

Assume the product map is a bijection from the coordinate ball `B` of radius `r` onto
`coordCLE '' B`.

- `image_torusUnit_closedBall`: `torusUnit` maps the central ball onto `torusBall`.
- `restrict_image_torusChart`: Haar measure of the torus restricted to the image of the
  central ball under `torusChart` is `torusConst` times the pushforward of the restricted
  additive Haar measure. This is `restrict_torusBall_eq` translated on the right by `γ`,
  using right invariance.
- `image_orbitCoord_closedBall`: `orbitCoord '' B` is the product of the images of the two
  factor balls.
- `restrict_image_orbitCoord`: for `ν` compatible with right invariant Haar measures `μ` and
  `μT`, `(ν.prod μT)` restricted to `orbitCoord '' B` equals `identityConst μ` times the
  pushforward of `coordHaar γ` restricted to `B` under `orbitCoord`. It is the product of
  `restrict_image_cosetChart` and `restrict_image_torusChart`; their constants multiply to
  `identityConst μ`.

## The orbit map in coordinates

- `continuous_orbitMap`: the orbit map of any commutative subgroup is continuous, since its
  composite with the open quotient map is.
- `val_orbitMap_orbitCoord`, `orbitMap_orbitCoord`: on `B`, the orbit map at
  `orbitCoord x` is `unitOf (conjChart γ x) · γ`; in particular `conjChart γ x` is a unit
  (`isUnit_conjChart`).
- `continuousOn_conjChart`, `measurable_orbitCoord`: regularity of the charts.

## The pushforward at the base point

`map_restrict_image_orbitCoord`: suppose moreover that the conjugation chart is a bijection
from `B` onto its image with the pushforward identity of `exists_conjChart_pushforward`, and
that its image lies in `ringBall hγ r'` for an admissible `r' ≥ r`. Then

`((ν.prod μT).restrict (orbitCoord '' B)).map orbitMap = chartScale • μ.restrict (orbitMap '' (orbitCoord '' B))`.

The source becomes `identityConst μ` times the image of restricted coordinate Haar measure.
By `orbitMap_orbitCoord` its pushforward is the image under `u ↦ u γ` of the image under
`unitOf` of the conjugation chart pushforward. That pushforward is `chartScale` times
`ringHaar` restricted to the chart image `P`. Near the identity,
`map_val_restrict_of_subset_unitBall` (radius `r'`) identifies the image of
`ringHaar.restrict P` under `unitOf` with `(identityConst μ)⁻¹` times `μ` restricted to the
units with values in `P`. Right translation by `γ` preserves `μ`, and the two constants
cancel because `identityConst` does not depend on the radius.

## Existence

`exists_isSmallRadius` and `isSmallRadius_of_le` provide admissible radii;
`cosetChart_zero`, `torusChart_zero`, `orbitCoord_zero` and `continuousOn_orbitCoord` locate
the base point. The main result is `exists_orbitMap_localPushforward`: inside every
neighbourhood `N` of `(T · 1, γ)` there is an open set `W ∋ (T · 1, γ)` such that the orbit map
restricted to `W` is an open embedding and
`((ν.prod μT).restrict W).map orbitMap = chartScale • μ.restrict (orbitMap '' W)`.
Take `W = orbitCoord '' B` for a radius `r` below the radii of
`exists_productMap_pushforward` and `exists_conjChart_pushforward`, small enough that the
conjugation chart maps `B` into an admissible `ringBall` and `orbitCoord` maps `B` into `N`.
`W` is open as a product of a coset image (`isOpen_image_cosetChart`) and a right translate of
`torusBall`. It is compact, and the orbit map is injective on it by `orbitMap_orbitCoord` and
injectivity of the conjugation chart, hence a closed embedding of `W`. Its range is the right
translate by `γ` of the units with values in the chart image, which is open since the chart
image equals the image of a closed ball under the homeomorphism `chartDerivative`.

## Origin

This is the local calculation behind the Weyl integration formula: near a regular point the
conjugation map from (torus cosets) × (torus) to the group is a local homeomorphism whose
Jacobian, in compatible Haar normalizations, is the absolute discriminant, so that it pushes
the product measure to the inverse absolute discriminant times Haar measure
(Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en caractéristique non
nulle*, Mém. SMF 124 (2011), II.2.10). The proof here is an internal derivation in additive
coordinates.
