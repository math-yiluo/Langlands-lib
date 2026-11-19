# Matched radius charts for affine quotients

Given a surjective algebra map `f` from `A` to `B`, compose the
polynomial presentation of `A` with `f` to present `B`. Both
polynomial loci then use the same weighted Tate algebra at each
radius. The first presentation's relations vanish in the second
chart, so the Tate quotient map to the second chart descends to
the first. This is `quotientRadiusMap`. Its effect on the original
algebras is `f`.

The quotient map from the Tate algebra to the second chart has
uniformly norm-controlled lifts. The Tate quotient map to the first
chart does not increase norms. Applying it to those lifts gives
norm-controlled lifts through `quotientRadiusMap`, proving
admissibility.

An analytic point is in a given chart precisely when its seminorm
satisfies that chart's bounds on the polynomial generators. A
point on the chart satisfies the bounds by the spectral and
coordinate norm estimates. Conversely, the seminorm comparison
constructs the chart point if the bounds hold. Since the quotient
presentation uses the images of the original generators, the bounds
hold in the source exactly when they hold at its image. Hence the
matched source chart is the full inverse image of the target chart.

These facts are internal consequences of the Library's polynomial
locus presentation, seminorm comparison and norm-controlled
affinoid quotients. The field is complete, ultrametric and
nontrivially normed, with independent universes for the field and
the two algebras.
