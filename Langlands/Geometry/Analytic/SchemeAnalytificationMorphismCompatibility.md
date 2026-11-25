# Center and rational-point compatibility for scheme analytification maps

These are internal proof lemmas for the unchanged
`SchemeAnalytificationMorphismStatement`. They treat schemes locally of finite type
over a complete, ultrametric, nontrivially normed field in any universe. The
scheme morphism is over that field. No separatedness or quasi-compactness is used.

`localCenter_morphismLocalMap` proves local center naturality directly from the
published affine `center_baseMap`. Naturality of the canonical affine scheme
isomorphisms and the restriction identity for a scheme morphism convert that
affine equality into an equality of points of the target scheme.

`exists_subordinate_chart` assumes the source-center preimage formula for affine
opens. Choose an affine neighborhood of the image of the center in the target;
then choose an affine neighborhood of the source center inside its inverse image.
The preimage formula lifts the analytic point to that source chart.
`center_map` applies the defining equation of `IsAnalytificationMap` on such a
chart and the preceding local center equality.

`rationalPoint_map` assumes center naturality for a function between the analytic
spaces, the rational-center formulas for source and target, and the singleton-fiber
property for rational centers in the target. Both analytic points then have center
equal to the image of the closed point of `Spec K` under the composite rational
point, so the target singleton-fiber property identifies them. This implication
uses neither continuity of the function nor center surjectivity.

`compatibility_of_range_and_seminorm_injective` uses the rational-center helpers in
[`AnalytificationCenterComparison`](AnalytificationCenterComparison.md),
reusing the published rational-center proofs. It proves both compatibility clauses from the source and target
chart preimage-range formulas and injectivity of point seminorms on target charts.
This exposes the precise remaining inputs without requiring center surjectivity.

`compatibility_of_center` specializes these lemmas using the scheme clauses of the
separate statement `AnalytificationCenterStatement` (proved in
`AnalytificationCenterProof`). The preimage formula supplies
center naturality, and the rational-center formulas and singleton fibers supply
rational-point naturality. This route uses no rational-point topology or affine
strong-map functoriality theorem. These helpers are conditional implications, and
do not by themselves prove the center theorem or the full scheme morphism
statement.

The mathematical provenance is the already published target and center statements:
Berkovich 1990, Theorem 3.4.1, its proof steps (2)–(3), and Remark 3.4.2;
Conrad–Temkin 2009, Theorem 2.2.3. Those statements' paired Markdown supplies the
registered original sources. The present neighborhood and singleton-fiber route
is an internal derivation for the Library's polynomial-locus and glued-space model.
