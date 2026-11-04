# Actual model diagrams and their fibre loci

This derived construction supplies actual cartesian comparisons for the
last fibre-property clause of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp. 5–6,
Theorem 3.4(2). The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This module prepares the geometric comparisons needed for filtered
descent; it does not assert that descent theorem.

For arbitrary schemes X and Y over S, a relative morphism f, and a
diagram D of schemes over S, `morphismDiagram` is the natural
transformation whose components are the published actual
`baseChangeMap` maps. Its source and target are the published actual
pullback diagrams from `EtaleEquivalenceRelation.Action.TargetLimit`.
No new model presentation or substitute point set is introduced.

The module proves that each base-changed relative morphism is a
cartesian base change of f. Each transition of either model diagram
is cartesian over the original base transition. Pasting and cancelling
these actual pullback squares shows that each naturality square of
`morphismDiagram` is cartesian. The same argument works for a supplied
cone: its model-cone legs are cartesian over the actual original cone
legs, and the limiting-base morphism and any stage morphism form a
cartesian square. These conclusions require neither a limiting-cone
witness nor finiteness, affineness or separation assumptions on the
models.

Base change therefore preserves affine transition maps. A
quasi-compact model over a compact stage is compact, and a
quasi-separated model over a quasi-separated stage has a
quasi-separated underlying space. These instances retain their
explicit relative hypotheses; affineness of a model is not assumed.
Together with the published limiting-cone construction, they provide
the topology hypotheses needed to apply constructible-set detection
to the actual target model diagram.

The published equalities for actual nonempty and geometrically
connected fibre loci apply to these cartesian squares. Thus the loci
of an actual base change are exactly the inverse images of the loci
of f. The loci at the cone's base are likewise inverse images of the
loci at any stage along the actual target-model cone leg. Connectedness
means geometric connectedness of the actual residue-field fibre's
structure morphism, not connectedness of the rational-point set.

Finally, Chevalley's theorem from pinned Mathlib identifies the
nonempty-fibre locus with a locally constructible set for a locally
finitely presented quasi-compact morphism. The proof rewrites this
locus as the actual image of the whole source. When the target is
compact and quasi-separated, local constructibility implies global
constructibility. No quasi-separatedness of f is needed for this
particular image assertion. The two theorems directly reuse
`Scheme.Hom.isLocallyConstructible_image`; they introduce no additional
geometric assumption.

The cartesian arguments reuse Worker 105's earlier complete relative
affineness and model-descent drafts, expressed here as reusable
construction properties in a distinct namespace. Constructibility of
the geometric-connectedness and componentwise pure-dimension loci,
pure-dimension base-change comparisons, and eventual descent of the
combined fibre property remain separate obligations. All schemes and
the indexing category lie in a common arbitrary universe.
