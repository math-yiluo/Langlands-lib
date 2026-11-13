# NYLL M010: finite extension degree targets

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
| M010.088 | `FiniteAbstractExtension.degree_coe` | 750–752 | `FiniteAbstractExtension.degree_coeStatement` |
| M010.091 | `FiniteAbstractExtension.relIndex_eq_degree` | 775–779 | `FiniteAbstractExtension.relIndex_eq_degreeStatement` |
| M010.092 | `FiniteAbstractExtension.extensionSubgroup_index_eq_degree` | 782–785 | `FiniteAbstractExtension.extensionSubgroup_index_eq_degreeStatement` |

All three targets keep implicit `{G : Type u} [Group G]
[TopologicalSpace G]` followed by explicit `(E : FiniteAbstractExtension G)`.
There is no degree datum argument. The first proposition states that the
natural coercion of the positive degree is `Nat.card E.quotient`; the
second equates the relative index of the field subgroup in the base subgroup
with that coercion; the third equates the index of the represented subgroup
inside the base with the same coercion. The field/base order is retained.

The underlying source finite-extension object and its degree are reused
unchanged. In particular its actual finite quotient and the locally supplied
nonempty quotient justify the positive `Nat.card` degree. These are finite-only
bridges to natural-valued subgroup indices, not definitions of an invariant
for arbitrary-index data.

For M010.092, source `CyclicCohomology.extensionSubgroup E.base E.field E.below`
is expanded to its exact Mathlib body
`E.field.toSubgroup.subgroupOf E.base.toSubgroup`, as explicitly authorized
by the task. The original abbreviation is M004.002 in
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54
(file SHA-256 `06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`).
Its telescope is `{G : Type u} [Group G] [TopologicalSpace G]
(K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup)`; the
containment proof is unused and is still retained in `E`. Mathlib
`Subgroup.subgroupOf` is comap by the ambient subgroup inclusion, at pin
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 198 prefixes namespaces, narrows imports, expands that abbreviation,
and converts the source theorem commands to Prop-valued definitions ending
in `Statement`. The original proofs and simp attributes are omitted.
No proof, extra hypothesis or instance is introduced.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
