# NYLL M010.019: cardinality of the residue quotient

Worker 289 adapts Naganori Yamaguchi's theorem
`ClassFormation.DegreeData.residueDegreeCardinal_eq_mk_residueQuotient` as
`Langlands.NYLL.ClassFormation.DegreeData.residueDegreeCardinal_eq_mk_residueQuotient`.
Its result type is exactly the published
`Langlands.NYLL.ClassFormation.DegreeData.residueDegreeCardinal_eq_mk_residueQuotientStatement D K`.
The parameters are implicit `G : Type u`, `[Group G]`, `[TopologicalSpace G]`,
then explicit `D : DegreeData G` and `K : ClosedSubgroup G`. Unfolding the
target gives
`D.residueDegreeCardinal K = Cardinal.mk (D.residueQuotient K)`.
There are no added hypotheses.

The only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements`.
The target and its paired Markdown were read at Library commit
`ed924aef420de137b4cbaa3b063a3618afcd73fd` and in the workspace base
`7dc9118a3eb340e83e65d6e4174763b7a61e573c`.
The imported `Fields.Definitions` defines `residueDegreeCardinal` using
`relativeIndexCardinal` for the inclusion `D.fieldImage K ≤ ⊤`.
The published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U010.Definitions`
defines `relativeIndexCardinal` by `intersectionIndexCardinal`, which is
`Cardinal.mk` of the corresponding coset type. Thus both sides reduce to
`Cardinal.mk ((⊤ : Subgroup ZHatMul) ⧸ (D.fieldImage K).subgroupOf ⊤)`.
The implemented proof is `rfl`, as in the source. It invokes no index
theorem or extra assumption, and does not use `D.degree_surjective`.
The quotient, subgroup and cardinal infrastructure and the actual NYLL
profinite-integer closure model are provided transitively by the published
target's imports; no additional supporting module is introduced.

The original is source unit M010.019 in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
from `n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Its docstring is at line 144,
`@[simp]` and the theorem name at line 145, the signature through line 147,
and the `rfl` body at line 148. The retained source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`;
its SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The registered collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplementary registration is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The modifications are the focused module path, namespace prefix
`Langlands.NYLL`, replacement of the source import list by the published
target import, and use of the named proposition as the result type.
The unused source `noncomputable section` and opening of `CyclicCohomology`
are omitted. The source name, universe, parameter order, docstring, `rfl`
proof and `@[simp]` attribute are retained. The published target and its
dependencies are unchanged.

The original copyright, author and Apache-2.0 header are retained.
The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are preserved unchanged. This equality identifies a residue cardinal with
the cardinality of its actual quotient; it discharges no host
class-formation, cup, transfer, Tate or reciprocity target.
