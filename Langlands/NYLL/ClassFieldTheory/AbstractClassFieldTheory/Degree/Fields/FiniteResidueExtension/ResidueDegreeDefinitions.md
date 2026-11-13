# NYLL M010: finite-residue extension relative residue degree

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
| M010.116 | `FiniteResidueAbstractExtension.residueDegree` | 1058–1060 | `FiniteResidueAbstractExtension.residueDegree` |

This definition keeps implicit `{G : Type u} [Group G]
[TopologicalSpace G]`, implicit `{D : DegreeData G}`, and explicit
`(E : FiniteResidueAbstractExtension D)`. The codomain is the positive
naturals `ℕ+`. Its body is exactly the source expression
`E.toFiniteAbstractExtension.residueDegree D`.

The existing forgetful constructor retains the actual endpoint subgroups,
their containment and their relative finite quotient proof. The imported
positive relative residue degree is the `Nat.card` of the mapped-subgroup
coset type paired with its actual positivity proof. The endpoint bundles
also retain their original absolute residue-finiteness data; no new
finiteness, cardinal inequality or equality is taken as a parameter.

Worker 198 changes only the enclosing namespace and focused imports,
retaining the source `noncomputable def`, telescope, body and result type.
No extra instance or theorem proof is introduced.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
