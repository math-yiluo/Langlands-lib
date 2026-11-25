# Local calculus for varying-dimension point atlases

This internal development supports uniqueness of admissible varying-dimension
analytic structures. It derives local calculus directly from the published
`DimensionPointAtlas.AnalyticOn` definition; it introduces no geometric
assumptions.

`AnalyticAt` requires continuity at the original rational point and analytic
coordinate expressions for every source and target chart containing the point
and its image. Analytic maps on open subsets give this property. Conversely,
pointwise analyticity everywhere gives an analytic map on the entire space.
The property is unchanged by equality on a neighborhood.

The composition proof chooses the supplied intermediate chart at the image.
The two coordinate expressions compose by `ContDiffAt.comp`. Continuity ensures
that the intermediate image remains in that chart near the point, so its inverse
law identifies this expression locally with the coordinates of the composite.
This works for every pair of outer chart dimensions. No analytic transition
assumption, henselian hypothesis, or completeness hypothesis is used.

`analyticMap_comp_model` composes an analytic map to a finite coordinate space
with an analytic map from that coordinate space. It applies `ContDiffAt.comp`
inside each pair of outer charts, using continuity to obtain neighborhoods from
the full coordinate domains.
