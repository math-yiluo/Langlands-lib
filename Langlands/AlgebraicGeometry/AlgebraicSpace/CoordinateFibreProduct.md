# Fibre products on coordinate point topologies

Author: Worker 105.

Helper module for the fibre-product clause of Conrad's p.17 claims
(`Langlands.Global.AdelicSpacePointTopologyStatement`).

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinateFibreProduct`.

- `isLocallySeparated_of_isSeparated`: separated algebraic spaces are locally separated. A closed
  immersion is an immersion (`MorphismProperty.relative_monotone`).
- `isPullback_hom`: a pullback square in the category of algebraic spaces is a pullback square of
  the underlying presheaves.
  - Every object of the site is a scheme `T`, and sections over `T` are maps from the space of `T`
    (Yoneda).
  - So the universal property of the square gives existence and uniqueness of sections over
    each `T`.
  - `Types.isPullback_iff` and `IsPullback.of_forall_isPullback_app` then conclude.
- `isPullback_baseChange`: base change of algebraic spaces keeps pullback squares of presheaves.
  It is precomposition with `Over.map`, computed objectwise.
- `coordinate_eq_iInf`: `coordinatePointTopology` is the infimum over the factors of the
  topologies induced from the field-valued topologies.
- `fieldValued_eq_induced`: the setting is
  - a pullback square `P = X ×_Z Y` of separated spaces of finite type over `C`;
  - a map `φ : A → L` to a henselian valued field.

  Then the field-valued topology on `P(A)` is induced along `P(A) → X(A) × Y(A)`. The base-changed
  square over `L` is a pullback, so its rational points embed in the product
  (`isEmbedding_pullbackPoints`). The field-valued point maps are natural
  (`CoordinatePointMaps.fieldValuedPointMap_map`).
- `coordinate_eq_induced`: if every factor topology of `P` is induced from `X × Y`, so is the
  coordinate topology. Both sides are infima over the factors (`iInf_inf_eq`).
