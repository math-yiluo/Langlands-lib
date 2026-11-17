# Hausdorffness detected on pairs of affine analytic charts

This internal reduction is a general topological argument for the actual
published `SchemeAnalytification.Space`. `ChartRelationClosed K f` asserts that
for each pair of affine opens `U` and `V`, the set of pairs of analytic chart
points with equal images under `ι` is closed in
`LocalSpace K f U × LocalSpace K f V`, with its ordinary product topology.

`t2Space_iff_chartRelationClosed` proves that this predicate is equivalent to
Hausdorffness of the glued space, assuming every canonical chart map `ι` is
an open map. For a Hausdorff target, the chart equality relation is the inverse
image of the closed diagonal under a continuous map. Conversely, represent two
distinct target points in two charts. The complement of the closed chart
relation contains a product of open neighborhoods of the representatives.
Their images under the open chart maps are disjoint open neighborhoods of the
original points.

The result is derived directly from general topology and the published
surjectivity of the family of charts. It uses no literature-specific claim,
no algebraic separatedness hypothesis, and no identification of an analytic
fiber product with a product of topological spaces. It does not prove
closedness of the chart relations or either direction of the separatedness
criterion. The complete ultrametric nontrivially normed field and locally
finite type scheme hypotheses are those of the published space, in every
universe.
