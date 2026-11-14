# NYLL M010.020: residue cardinal of the distinguished base field

Worker 238 adapts Naganori Yamaguchi's
`ClassFormation.DegreeData.residueDegreeCardinal_baseField` as
`Langlands.NYLL.ClassFormation.DegreeData.residueDegreeCardinal_baseField`.
Its result is exactly the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.residueDegreeCardinal_baseFieldStatement D`,
which unfolds to `D.residueDegreeCardinal (baseField G) = 1`. The parameters
remain implicit `G : Type u`, `[Group G]`, `[TopologicalSpace G]`, followed
by explicit `D : DegreeData G`. The surjectivity used in the proof is the
existing field `D.degree_surjective`. No finiteness, compactness,
topological-group or extra topology hypothesis is introduced.

The implemented proof retains the source body. The first `change` unfolds
the published target, `residueDegreeCardinal` and `relativeIndexCardinal`
to the corresponding `intersectionIndexCardinal`. The published
`D.fieldImage_eq_map` identifies the base-field image with the image of
its underlying subgroup. The published `baseField_toSubgroup` identifies
that subgroup with the whole ambient group. Mathlib's
`Subgroup.map_top_of_surjective`, applied to `D.degree_surjective`,
therefore identifies the image with the whole group `ZHatMul`.
The second `change` unfolds the cardinal index to
`Cardinal.mk (↥(⊤ : Subgroup ZHatMul) ⧸ ⊤) = 1`.
The subgroup-of-top expression reduces definitionally to the full subgroup.
`QuotientGroup.subsingleton_quotient_top` supplies a local subsingleton
instance on this quotient. Its canonical identity coset supplies
inhabitedness, and `Cardinal.mk_eq_one` proves that its cardinality is one.
This is the cardinality of the actual coset type, without passing through
a natural-valued index.

The direct imports are the published support modules
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U004.Proofs`
and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs`.
They import the unchanged `Fields.Statements` and `Fields.Definitions`,
including the actual degree datum, base field, field image and cardinal
index definitions, and the needed Mathlib quotient and cardinal results.
No additional helper module or new mathematical assumption is used.

The original source is unit M010.020 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
in `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The original docstring is
lines 150–151, the signature with `@[simp]` is lines 152–153,
and the proof body is lines 154–163. The readable source is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`.
Its SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplementary registration is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public routing reference is `notes/reuse/nyll-public-port-plan.md`
and its M010.020 row in `notes/reuse/nyll-public-port/m001-m024.md`.

The source modifications are extraction into the focused U020 proof module,
the `Langlands.NYLL` namespace prefix, the two focused proof imports in
place of the broad original import list, and use of the published named
proposition as the result type. The unused opening of `CyclicCohomology`
is omitted. The source's `@[simp]` attribute is omitted, as in U004;
the theorem is available for explicit rewriting. The source theorem name,
docstring, universe, parameter order, hypotheses, noncomputable section
and proof body are retained.

The original copyright, Apache-2.0 license and author header are retained.
The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are preserved unchanged.
