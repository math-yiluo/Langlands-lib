# NYLL M010.011: the field image as a subgroup map

This file proves the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.fieldImage_eq_mapStatement`
with the source-adapted theorem
`Langlands.NYLL.ClassFormation.DegreeData.fieldImage_eq_map`.
Its parameters are implicit `G : Type u`, `[Group G]`,
`[TopologicalSpace G]`, followed by explicit `D : DegreeData G` and
`K : ClosedSubgroup G`. Its declared result is exactly
`fieldImage_eq_mapStatement D K`, asserting
`D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom`.

The original is Naganori Yamaguchi's
`ClassFormation.DegreeData.fieldImage_eq_map`, source unit M010.011,
in `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The docstring is line 96, the signature is lines 97–98, and the proof
ends at line 104. The source file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplementary registration is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public routing reference is
`notes/reuse/nyll-public-port-plan.md`, with its M010.011 row in
`notes/reuse/nyll-public-port/m001-m024.md`.

The implemented proof follows the original. A `change` step unfolds the
published proposition to the subgroup equality. Subgroup extensionality
reduces it to membership equivalence at each `z : ZHatMul`. A witness
`k : K.toSubgroup` in the range of the restricted degree yields the
subgroup-map witness `⟨k.1, k.2, rfl⟩`. Conversely, a subgroup-map
witness `g : G` with `hg : g ∈ K.toSubgroup` yields the range witness
`⟨⟨g, hg⟩, rfl⟩`. These reflexive equalities use the definition of
`restrictedDegree` as composition with the subgroup inclusion.

The sole direct import is the published `Fields.Statements` module. Its
`Fields.Definitions` import supplies `fieldImage`, `restrictedDegree`,
`DegreeData`, and the underlying closed subgroup and degree objects.
The proof uses Mathlib subgroup extensionality, the definitions of
`MonoidHom.range` and `Subgroup.map`, and subtype constructors. It does
not use a separate restricted-degree evaluation theorem or the degree's
surjectivity proof. The source universe, parameter order and hypotheses
are preserved. This support equality supplies no host class-formation,
cup, transfer, Tate or reciprocity result.

Worker 188 extracts this theorem into the focused U011 proof module,
prefixes its namespace with `Langlands.NYLL`, replaces the broad source
imports with the published statement import, and adds the named-target
`change` step. The original proof body and author/copyright header are
retained. Apache-2.0 attribution remains in `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
