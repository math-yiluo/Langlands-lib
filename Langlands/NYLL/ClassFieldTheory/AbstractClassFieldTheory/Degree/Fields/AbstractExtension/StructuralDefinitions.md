# NYLL M010: abstract towers and ramification predicates

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
| M010.037 | `AbstractExtension.Tower` | 304–316 | `AbstractExtension.Tower` |
| M010.038 | `AbstractExtension.Tower.topExtension` | 322–326 | `AbstractExtension.Tower.topExtension` |
| M010.039 | `AbstractExtension.Tower.baseExtension` | 328–332 | `AbstractExtension.Tower.baseExtension` |
| M010.040 | `AbstractExtension.Tower.totalExtension` | 334–338 | `AbstractExtension.Tower.totalExtension` |
| M010.044 | `AbstractExtension.IsUnramified` | 372–377 | `AbstractExtension.IsUnramified` |
| M010.045 | `AbstractExtension.IsTotallyRamified` | 379–383 | `AbstractExtension.IsTotallyRamified` |

The structure keeps the source telescope
`(G : Type*) [Group G] [TopologicalSpace G]` and exactly its three
closed-subgroup fields and two contravariant containment proofs.
The three constructors retain the implicit universe-`u` group and instances,
explicit `T : Tower G`, and the exact source structure field assignments,
including `T.top_le_middle.trans T.middle_le_base` for the composite.
M010.038–040 are necessary additional source-module dependencies of the
required tower target M010.041 and finite-tower structure M010.105.

The two predicates keep implicit `{G : Type u}` and its group/topology
instances, explicit `(E : AbstractExtension G)` followed by `(D : DegreeData G)`.
Unramifiedness is the actual base-inertia containment; total ramification is
the reverse degree-image containment. Neither predicate is replaced by a
natural-valued index equality or a finiteness condition.

Worker 198 makes only namespace and import changes for these six data
commands. Their bodies, fields, proof terms, binder kinds and universe
generality are retained. No instance or theorem proof is introduced.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
