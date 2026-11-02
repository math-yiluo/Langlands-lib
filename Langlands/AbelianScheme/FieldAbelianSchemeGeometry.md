# Basic geometry of an abelian scheme over a field

This module covers an abelian scheme `A` over `Spec K`, for a field `K`, with
underlying scheme `A.X.left`. Smoothness, properness and geometric
connectedness are fields of the `AbelianScheme` bundle.

- `field_isIntegral`: `A.X.left` is integral. The published theorem
  `smoothGeometricIntegrality` makes the structure morphism geometrically
  integral, and Mathlib's `GeometricallyIntegral.isIntegral_of_subsingleton`
  then gives integrality, because `Spec K` has one point.
- `field_isNoetherian`: `A.X.left` is Noetherian. It is locally Noetherian, as
  it is locally of finite type over a field, and compact, as it is
  quasi-compact over the one-point space `Spec K`.
- `field_isSeparated`: `A.X.left` is separated. Its morphism to the terminal
  scheme is the proper (hence separated) structure morphism composed with the
  separated morphism from the affine scheme `Spec K`.
- `field_closedPoint_stalk_dimension`: if `A` has relative dimension `g`, the
  stalk at every closed point has Krull dimension `g`. This applies the
  published theorem `fieldSmoothClosedPointStalkDimension`.
- `field_topologicalKrullDim`: if `A` has relative dimension `g`, then
  `topologicalKrullDim A.X.left = g`.
  - The upper bound is the published theorem `fieldSmoothTopologicalKrullDim`.
  - For the lower bound, the closed set `univ` contains a closed point `x`.
    The stalk dimension at `x` is `g`, and it equals the coheight of `x`
    (`ringKrullDim_stalk_eq_coheight`). That coheight is at most the Krull
    dimension of the space.

  The argument is the same as the dimension step in the published proof
  `smoothProperConnectedFiniteFlatGeometry`.

## Provenance

These are standard properties of abelian varieties over a field. They are
derived from the published results named above, and no separate source
statement is cited. They supply hypotheses for the Bezout count in the
reduction of
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
(Mumford–Fogarty–Kirwan, GIT 3rd ed., Prop. 7.7): integral, Noetherian,
separated, dimension `g`, and stalk dimension `g` at the counted closed points.
They do not prove that target.
