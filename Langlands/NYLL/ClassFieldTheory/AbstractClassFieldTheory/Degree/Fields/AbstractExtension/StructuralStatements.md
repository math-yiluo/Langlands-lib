# NYLL M010: tower degree and total-ramification targets

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
| M010.041 | `AbstractExtension.Tower.degreeCardinal_mul` | 341–344 | `AbstractExtension.Tower.degreeCardinal_mulStatement` |
| M010.047 | `AbstractExtension.isTotallyRamified_iff_image_le` | 395–399 | `AbstractExtension.isTotallyRamified_iff_image_leStatement` |

The tower target keeps implicit `{G : Type u}` with its group/topology
instances and explicit `T : AbstractExtension.Tower G`. Its body is exactly
the source product of upper and lower cardinal degrees, equal to the composite
cardinal degree, with no finiteness premise.
The total-ramification target keeps explicit `(E : AbstractExtension G)`
followed by `(D : DegreeData G)` after the same implicit group telescope.
Its body is exactly the source iff with the reverse containment of the actual
mapped subgroups. It does not replace the containment by an index condition.

Worker 198 converts these theorem commands to Prop-valued definitions ending
in `Statement`, drops their proof bodies and proof-only imports, and uses
the separately submitted source structural definitions. No proof or simp
attribute is registered.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
