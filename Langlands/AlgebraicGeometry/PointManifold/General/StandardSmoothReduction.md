# Universe-general reduction of regular atlas existence to standard-smooth affine charts

This module adapts the published `PointManifold.StandardSmoothReduction` implementation by Worker 135
to `PointManifold.General`, with an explicit arbitrary coefficient universe
`u` and `k : Type u`. Worker 1650 made this universe extension. It uses the
published actual `RingPoint` carrier and evaluation topology, and leaves the
existing target and all its imported definitions unchanged. The construction
places no positive-dimension or point-nonemptiness premise on its input.

This internal construction separates the algebraic localization and covering
argument from the analytic chart construction. `RegularAtlas.ofStandardSmooth`
assumes a pointwise chart construction for every affine `Y` whose actual
coordinate algebra is standard smooth over `k` in dimension `d`. Under the
algebraic assumption `SmoothOfRelativeDimension d X.hom`, it constructs
`RegularAtlas k X d`. The accompanying theorem
`regularChartExistence_of_standardSmooth` packages this implication using the
exact Library proposition `regularChartExistenceStatement`.

For an actual point `p`, the proof applies
`standardSmoothPrincipalNeighborhood` to its closed-point image. The resulting
principal open has a standard-smooth actual coordinate algebra and contains the
whole image of `p`: containment in an open is determined by the closed-point
image for a point over a local ring, and a field is local. The actual morphism
`p` therefore factors through that principal open by `openPointLift`.
The assumed pointwise chart construction supplies a chart containing this
lift. `RegularChart.ofBasicOpen` transfers it back to `X`, including its rational
coordinate identities, nonvanishing denominators and smooth inverse
evaluations. Its source identity and the open-point factorization equation
show that the transferred chart contains `p`. Choice selects one such chart
for every point.

The construction includes zero dimension and empty actual point spaces: its
pointwise choice requires no inhabitedness premise. It is a conditional
reduction and does not by itself prove the analytic standard-smooth chart
input. Its provenance is the internal composition of the neighborhood and
chart-transfer constructions with the published actual open-point API.
