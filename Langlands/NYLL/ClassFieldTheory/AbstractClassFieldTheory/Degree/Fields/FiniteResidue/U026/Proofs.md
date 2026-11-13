# NYLL M010.026: the natural value of the positive residue degree

This file proves `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.residueDegree_coeStatement`
with the source-adapted theorem `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.residueDegree_coe`.

Its parameters are implicit `G : Type u`, `[Group G]`,
`[TopologicalSpace G]`, implicit `D : DegreeData G`, and explicit
`K : FiniteResidueAbstractField D`. Its type is exactly
`residueDegree_coeStatement K`, asserting
`(K.residueDegree : ℕ) = Nat.card (D.residueQuotient K.field)`.

The proof is `rfl`, following the original M010.026 at lines 201–203
(the next unit starts at 206). The definition `residueDegree` constructs
a positive natural whose underlying natural is this same `Nat.card`;
projection and unfolding the named target yield reflexivity. No separate
cardinality theorem or finiteness hypothesis is introduced. The bundled
finite-quotient proof belongs to the published object.

The sole direct import is `Fields.FiniteResidue.Statements`, which imports
the published `Fields.FiniteResidue.Definitions`. Those modules supply the
named target, `FiniteResidueAbstractField`, its `residueDegree`, and the
underlying residue quotient. There is no additional theorem dependency.
The source's `simp` attribute is omitted; the theorem is available for
explicit application. Its source telescope and proof body are preserved.

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
