# NYLL M010: finite-residue field coercion targets

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

All public names in the table use prefix
`Langlands.NYLL.ClassFormation.DegreeData.`, unless written in full.
Original names use prefix `ClassFormation.DegreeData.`.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M010.026 | `FiniteResidueAbstractField.residueDegree_coe` | 201–203 | `FiniteResidueAbstractField.residueDegree_coeStatement` |
| M010.027 | `FiniteResidueAbstractField.residueDegreeCardinal_eq_coe` | 206–212 | `FiniteResidueAbstractField.residueDegreeCardinal_eq_coeStatement` |

Both targets retain implicit `{G : Type u}`, `[Group G]`,
`[TopologicalSpace G]`, implicit `{D : DegreeData G}` and the explicit
`(K : FiniteResidueAbstractField D)`, with no separate finite instance premise.
The source object's finite residue quotient is unchanged. The first body
is the natural coercion equality with `Nat.card (D.residueQuotient K.field)`;
the second is the Type-zero cardinal equality with the natural coercion
of the same positive residue degree.

Worker 198 converts source theorems to `def ...Statement : Prop := ...`,
omits theorem proof bodies and their `simp` attributes, and narrows the import
to the published finite-residue data. In particular no simp lemma or proof
of either proposition is registered by these targets.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
