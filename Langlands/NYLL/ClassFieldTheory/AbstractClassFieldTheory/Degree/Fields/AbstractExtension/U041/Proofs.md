# NYLL M010.041: cardinal degrees multiply in an arbitrary tower

This file proves `Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension.Tower.degreeCardinal_mulStatement`
with the source-adapted theorem `Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension.Tower.degreeCardinal_mul`.

Its parameters are implicit `G : Type u`, `[Group G]`,
`[TopologicalSpace G]`, then explicit `T : AbstractExtension.Tower G`.
Its type is exactly `degreeCardinal_mulStatement T`, stating
`T.topExtension.degreeCardinal * T.baseExtension.degreeCardinal =
T.totalExtension.degreeCardinal` in `Cardinal.{u}`. No finiteness or
normality assumption is added.

The implementation follows M010.041, lines 341–344 (the next unit starts
at 348). Apply the published
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_mul` to
`T.top_le_middle` and `T.middle_le_base`. Unfolding the named targets,
the three extension projections and `AbstractExtension.degreeCardinal`
identifies its upper, lower and composite relative indices with the three
cardinal degrees. These are definitional reductions, so the source's
single `exact` proof works unchanged.

The direct imports are `Fields.AbstractExtension.StructuralStatements`
and `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U014.Proofs`.
The former supplies the target, tower projections and cardinal-degree
definition. The latter supplies the substantive multiplicativity theorem;
its published proof derives cardinal equality from the quotient-tower
equivalence and Mathlib cardinal products. This proof does not assume
multiplicativity as a new premise and does not use residue- or
ramification-degree multiplicativity. The full source telescope, factor
order, infinite-cardinal scope and proof route are preserved.

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The routing reference is `notes/reuse/nyll-public-port-plan.md`, with M010's
unit rows in `notes/reuse/nyll-public-port/m001-m024.md`.

Worker 188 extracts this focused proof, prefixes its namespace with
`Langlands.NYLL`, narrows the source imports to the published modules
listed above, and states the result using the exact published named target.
The original copyright, Apache-2.0 and author header is retained.
The unchanged attribution files are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support theorem supplies no host class-formation, cup, transfer, Tate
or reciprocity result.
