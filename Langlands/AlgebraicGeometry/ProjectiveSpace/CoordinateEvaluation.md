# Evaluating actual projective affine charts

Author: Worker 105. This internal construction is a prerequisite for the bounded
chart argument for projective-point compactness over locally compact fields.
The motivating source is Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), Proposition 4.4, printed p.11. No compactness theorem is asserted
in this construction.

For a homogeneous vector `a : Fin (n+1) → K` over an arbitrary field in an
arbitrary universe, and any nonzero coordinate `a j`, `coordinateChartMap`
constructs the actual K-algebra map from the j-th projective affine chart to K.
It restricts polynomial evaluation through the ordinary localization away from
`X j` to its degree-zero homogeneous localization. Its value on `X k / X j` is
exactly `a k / a j`.

The construction uses the existing Library projective scheme and chart rings.
For the existing normalized homogeneous coordinates of any actual rational
scheme morphism, evaluating in any nonvanishing chart recovers the same actual
morphism. The proof applies the published two-chart comparison to the old and
new coordinate maps. No topology is assigned to projectivization or assumed as
an input, and no compactness or properness result is used.
