# Eventual equality and uniqueness of algebraic-space models

## Source and scope

This proves exactly `Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitUniquenessStatement.{u}` from the unchanged published statement pair. It is the injectivity part of Theorem 3.4(1) and the model-uniqueness assertion of Theorem 3.4(3) in Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), extended to quasi-separated algebraic spaces on printed p.13. The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed pp.5 and 13 were read.

The proof retains the arbitrary universe, small cofiltered index category, affine scheme diagram and supplied limit cone. Source and target spaces carry exactly the target's quasi-separatedness and locally-finitely-presented, quasi-compact atlas hypotheses. There are no extra hypotheses.

## Implemented proof

`hom_ext_atlas` shows that a morphism is determined by its value on the universal point of an etale surjective scheme atlas. Every section lifts along an etale surjection to an atlas point. Naturality and injectivity of pullback along that cover then establish equality on all sections.

`eventual_eq` chooses an affine atlas using quasi-compactness of the original atlas over the affine base. Base changing this affine atlas along the diagram produces another cofiltered diagram of affine schemes with its actual limit. The two morphisms give two sections of the target over the atlas. Equality of the morphisms over the limit gives equality of these sections over the new limit. `SpaceFilteredPoints.exists_eq_of_limit` detects equality at a stage, and `hom_ext_atlas` gives equality of the entire stage morphisms. Restriction of the original diagram to the over-category of the given index yields `spaceLimitMorphismEventualEquality`. This argument uses weaker premises internally, without changing the exact target.

`rebase` transports a morphism between two base changes along a map of schemes over their common base. It conjugates ordinary `baseChangeMap` by the published `BaseChangeComparison.compIso`. Its compatibility with identities and composition follows by cancellation of inverse comparisons. The coherence theorem `rebase_rebase` is proved on sections: the relevant over-isomorphisms have identity underlying scheme maps, and naturality gives compatibility along successive reindexings.

`exists_rebase_map` expresses the published quasi-separated morphism-descent theorem with `rebase`. To prove `exists_rebase_iso`, descend the prescribed isomorphism and its inverse separately, then choose a common index by cofilteredness. Their two composites equal the respective identities over the limit. Apply the proved eventual-equality result to each composite and choose a further common stage over that index. At this stage both inverse identities hold, producing an actual isomorphism. Solving the comparison equation gives exactly the target's prescribed `compIso` compatibility.

The essential uniqueness of two stage isomorphisms follows immediately from `spaceLimitMorphismEventualEquality` applied to their hom components. Quasi-separatedness and the atlas properties persist after base change. `spaceLimitUniquenessStatement` pairs the two exact clauses.

## Published inputs and provenance of helpers

The proof imports `SpaceLimitMorphismDescentQuasiSeparatedProof`, whose import closure contains the published modules `SpaceLimitMorphismDescentProof` and `SpaceFilteredRingPointProof`. Their atlas, section-comparison and morphism-descent constructions originate in Worker 208's proofs. These inputs are used by their Lean names. The iterated-base-change comparisons come from the unchanged published `SpaceBaseChangeComparison`.

Worker 130 supplies the new equality, comparison-coherence and isomorphism-assembly helpers as internal deductions implementing the route described above. The endpoint proves only the two clauses of the named uniqueness target; model existence and property descent remain separate results.
