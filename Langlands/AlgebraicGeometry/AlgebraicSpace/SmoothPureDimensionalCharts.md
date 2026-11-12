# Affine source charts in the prescribed relative dimension

This is an internal prerequisite for Conrad's Proposition 5.4 analytic-manifold assertion (printed pp.15–16). It constructs an actual affine scheme mapping etale to the algebraic space, with a rational point above the specified rational point and a structure morphism smooth of exactly the prescribed relative dimension. The input is the unchanged `IsSmoothPureDimensional` predicate, not a supplied analytic atlas.

The relative dimension of the existential good atlas transfers to every etale scheme chart. Form the represented pullback of the good atlas and the given chart. Its projection to the chart is etale and surjective, and its projection to the good atlas is etale. Composition gives the prescribed dimension on the pullback; the field-base etale source-descent theorem then gives that dimension on the given chart.

The published rational-point lifting theorem supplies the affine chart and lifted point. Smoothness makes this a finite-type chart. Over a complete nontrivially normed field, the existing henselian-field results make its point map continuous, open and locally injective when the algebraic space is locally separated. Hence it is a local homeomorphism for the existing affine point topology and the etale-chart topology. The published analytic affine construction supplies a regular analytic atlas on its actual source points.

These are source-chart data. Analytic compatibility between different source charts, the manifold structure on space points, functoriality, affine-space normalization and uniqueness of the final family remain to be proved.
