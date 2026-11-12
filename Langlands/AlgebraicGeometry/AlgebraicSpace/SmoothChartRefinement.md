# Common affine refinements of smooth point charts

This internal construction serves the analytic gluing step in Conrad's Proposition 5.4 (printed pp.15–16). Given two affine etale charts with structure maps smooth of relative dimension `n`, and a point of each with the same image in the algebraic space, it constructs a common affine scheme with etale projections and a rational point projecting to those two points. Its structure map remains smooth of relative dimension `n`.

The represented fibre product supplies a rational point with the prescribed projections. That point factors through an affine open neighborhood. Both projections are etale by base change and composition with the open immersion. Composing the first projection with the first chart's structure map proves the relative-dimension assertion. The presheaf pullback square gives the commuting equation, both as natural transformations and on every actual rational point.

Over a complete nontrivially normed field, `contMDiffAt_branch_transition` proves analyticity of the change between any two topological branches of these point maps, for the regular analytic structures on their affine sources. The common refinement has a regular analytic atlas of the same dimension. Its etale projections are analytic local diffeomorphisms by the published affine theorem. Compose the second with the analytic local inverse of the first, and use the commuting point equation and branch inverse identities to identify the composite with the transition on a neighborhood. The general topological/analytic argument is in `Langlands/Geometry/Manifold/EtaleChartGluing`.

The two anchor points of the original chosen charts may be different; the comparison applies at every point in the overlap, not only at those anchors.
