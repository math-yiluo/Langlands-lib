# The group law on split infinitesimal points at the identity

Module `Langlands.AlgebraicGeometry.Deformation.SplitPointGroupLaw` (namespace
`Langlands.AlgebraicGeometry.SplitInfinitesimalCoordinates`).

Let `G` be a group scheme over a field `k` and `c` a point chart of `G` at its identity
(`PointChart`, from `SplitInfinitesimalCoordinates`). For a `k`-algebra `D` and a `D`-module `M`,
the split points `c.Points (D := D) (M := M)` are the maps from the split square-zero test
`Spec (D ⊕ M)` to `G` whose reduction to `Spec D` is the identity point.

- `PointChart.mul` is the pointwise product of two such points in the group of maps into `G`.
- `PointChart.mapPoints_mul`, `mapPoints_comp`, `mapPoints_id`, `mapPoints_zero`: the functoriality
  of split points in the coefficient module (`mapPoints`) commutes with products, compositions and
  identities, and the zero map of modules sends every point to the identity point.
- `PointChart.linearCoordinates_mul`: the linear cotangent coordinates of a product are the sum of
  the coordinates, `c.linearCoordinates (c.mul v w) = c.linearCoordinates v + c.linearCoordinates w`.

## Proof of `linearCoordinates_mul`

Put `v` on the first and `w` on the second summand of `M × M` (by `mapPoints` along `inl` and
`inr`) and multiply the two resulting points. Pushing this product forward along the first and the
second projection gives back `v` and `w`, because the other factor becomes the identity point;
pushing it forward along the sum map `M × M → M` gives `c.mul v w`. Linear coordinates are natural
in the coefficient module (`linearCoordinates_mapPoints` in `SplitInfinitesimalCoordinates`), and
the sum map is the sum of the two projections, which gives the formula.

## Provenance

This is the familiar fact that, to first order at the identity, the group law of a group scheme
is addition of tangent vectors. The module proves it for the point charts of the Library by the
argument above; it uses no source beyond the definitions in `SplitInfinitesimalCoordinates`.
