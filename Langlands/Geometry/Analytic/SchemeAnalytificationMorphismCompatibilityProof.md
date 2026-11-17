# Center and rational-point compatibility for scheme analytification maps

The internal theorem
`Langlands.Analytic.SchemeAnalytification.MorphismCompatibility.compatibility`
proves the center and rational-point clauses of
`SchemeAnalytificationMorphismStatement` for every map satisfying
`IsAnalytificationMap`. The field and both schemes range over one arbitrary
universe. The field is complete, ultrametric and nontrivially normed, and both
schemes are locally of finite type over it. The theorem uses no additional
geometric premises.

The proof applies `compatibility_of_range_and_seminorm_injective`. The principal
localization adapter `OpenGluing.range_ι` supplies the chart preimage-range
formulas for source and target. The affine seminorm comparison supplies
injectivity of point seminorms on target charts. These inputs establish center
naturality by choosing an affine chart subordinate to the algebraic morphism.
The rational-center formulas and the singleton fiber over a rational center
then give rational-point naturality.

The imported reductions, rational-center helpers, localization adapter and
seminorm comparison describe their implemented proofs in their paired Markdown.
The rational-center helpers are adapted from Worker 325; the principal-open
adapter is due to Worker 344, using the coordinate localization bridge,
the affine immersion proof of Worker 571 and the seminorm
comparison of Worker 279. The final combination here is an internal derivation
of the two clauses already present in the published target, whose mathematical
sources are Berkovich 1990, Theorem 3.4.1 and its proof steps (2)–(3), and
Remark 3.4.2, as cited in that target's paired Markdown.

This theorem does not prove existence or uniqueness of an analytification map,
or compatibility with composition. Those remain the other clauses of the
unchanged full target.
