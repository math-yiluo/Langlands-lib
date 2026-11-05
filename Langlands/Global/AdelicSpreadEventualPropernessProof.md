# Properness after an actual arithmetic enlargement

`adelicSpreadEventualProperness` proves
`Langlands.Global.AdelicSpreadEventualPropernessStatement` in arbitrary
universe `u`. The paired statement records the original source, the
derived arithmetic scope, and the remaining whole-paper obligations.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp. 5–6, Theorem 3.4(2), the
properness clause, and Remark 3.5; printed p. 11, the first paragraph of
the proof of Proposition 4.4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This is a derived arithmetic specialization of the general
filtered-limit theorem. Its actual integer diagrams and their
noetherian initial rings justify arbitrary perfect function-field
constants, potentially inseparable rational-function extensions, and
empty initial sets, extending the source's global-field and nonempty-set
conventions. No additional field, separation, or affineness premise is
introduced.

The private `isProper_baseChangeMap_iff` compares the two actual pullback
orders: the general relative descent theorem uses `pullback p X.hom`,
whereas `Over.pullback p` uses `pullback X.hom p`. The canonical pullback
symmetries commute with the induced model morphisms. Properness respects
these isomorphisms, giving the equivalence.

The private `finiteTypeModels_proper_iff_stage` works over a noetherian
initial ring with an actual filtered algebra diagram and colimit cocone.
The supplied finite-type schemes are locally noetherian. Their structure
morphisms are finitely presented and quasi-separated; cancellation from
the source structure map gives local finite presentation,
quasi-compactness and quasi-separatedness of the relative morphism.
The imported `spectrumProperDescent` then detects properness at an actual
stage of the supplied diagram. The first helper changes both sides to
the literal `Over.pullback` maps.

The two public arithmetic clauses install the proved noetherianity of
the original outside-set integer ring and apply this helper to
`curvePlaceSIntegersOverDiagram` or `numberFieldSIntegersOverDiagram`.
Their proved colimit cocones have the original field as vertex and the
literal integer inclusions as legs. Thus both sides specialize to
exactly the displayed generic-fiber and arithmetic base-change
morphisms. The final theorem conjoins the two clauses.

Worker 208 authored this arithmetic proof. The imported general
properness-descent proof is Worker 105's development and is reused by
Lean name. Worker 706 checked the shared proof against the published
prerequisites and prepared this proof-only pair for independent review.
Existence of arithmetic models or model morphisms for arbitrary field
schemes, intrinsic adelic properness, compactness, stabilization, and the
other whole-paper conclusions remain separate obligations.
