# NYLL M010: finite tower data

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
| M010.105 | `FiniteTower` | 910–919 | `FiniteTower` |
| M010.106 | `FiniteTower.topQuotientFinite` | 925–929 | `FiniteTower.topQuotientFinite` |
| M010.107 | `FiniteTower.baseQuotientFinite` | 931–935 | `FiniteTower.baseQuotientFinite` |

The structure retains the complete source telescope
`(G : Type*) [Group G] [TopologicalSpace G]` and extends the published
`AbstractExtension.Tower G`. Its two additional proof fields are precisely
`Finite toTower.topExtension.quotient` and
`Finite toTower.baseExtension.quotient`. These are the actual two adjacent
coset spaces; neither composite finiteness nor normality is assumed.

The two instances keep implicit `{G : Type u}` and its group/topology
instances, then explicit `(T : FiniteTower G)`. Each exposes the corresponding
concrete coset space and returns exactly the source field
`T.finiteTopQuotient` or `T.finiteBaseQuotient`.
No additional instance is registered.

Every source `CyclicCohomology.extensionSubgroup K L hLK`
is replaced by its exact Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup`.
M004.002 in `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`,
lines 47–54 (file SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`),
has complete telescope `{G : Type u} [Group G] [TopologicalSpace G]
(K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup)` and
this exact body. The containment proof is unused by the abbreviation and
remains in the source object. At the approved Mathlib pin
`5ed2965256430c3649e86755f9576b54eca72435`, `Subgroup.subgroupOf`
is comap by the inclusion of the ambient subgroup. This definitional
expansion is explicitly authorized by the task.

Worker 198 prefixes the namespace, narrows imports to the abstract-tower
data, and expands that abbreviation. The source structure fields and both
instance proof bodies otherwise remain unchanged. The unrelated later
finite-tower constructors M010.108–109 are not needed by these units.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
