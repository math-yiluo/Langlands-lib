# NYLL M010: Galois subextension data

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
| M010.052 | `GaloisSubextension` | 456–465 | `GaloisSubextension` |
| M010.053 | `GaloisSubextension.toAbstractExtension` | 471–476 | `GaloisSubextension.toAbstractExtension` |
| M010.054 | `GaloisSubextension.extensionQuotient` | 478–481 | `GaloisSubextension.extensionQuotient` |
| M010.055 | `GaloisSubextension.IsUnramified` | 483–485 | `GaloisSubextension.IsUnramified` |
| M010.056 | `GaloisSubextension.IsTotallyRamified` | 487–489 | `GaloisSubextension.IsTotallyRamified` |
| M010.057 | `GaloisSubextension.extensionSubgroup_normalInstance` | 491–494 | `GaloisSubextension.extensionSubgroup_normalInstance` |
| M010.058 | `GaloisSubextension.extensionQuotient_groupInstance` | 496–501 | `GaloisSubextension.extensionQuotient_groupInstance` |
| M010.059 | `GaloisSubextension.extensionQuotientMulEquiv` | 503–508 | `GaloisSubextension.extensionQuotientMulEquiv` |
| M010.060 | `GaloisSubextension.extensionQuotientMk` | 510–513 | `GaloisSubextension.extensionQuotientMk` |

The source bundle retains implicit `{G : Type u}` and its `[Group G]`
and `[TopologicalSpace G]` instances, explicit `(K : ClosedSubgroup G)`,
and the three fields `field`, `below`, and `normal`. No finiteness is assumed.
The namespace commands retain implicit `{K : ClosedSubgroup G}`, explicit
`(L : GaloisSubextension K)`, and, for the two predicates only, explicit
`(D : DegreeData G)` following `L`.

The underlying extension has exactly the source endpoints and containment.
The named quotient remains a `def : Type u`. Its normal-subgroup instance
uses `L.normal`; the group instance unfolds that named quotient boundary
and invokes Mathlib's canonical quotient group structure, as in the source.
The comparison is `MulEquiv.refl _`, and the projection is the canonical
`QuotientGroup.mk'` on the actual subgroup.
Only the source instances are registered, with the same scope and predicates.
No extra canonical Mathlib instance is duplicated.

Every source `CyclicCohomology.extensionSubgroup K L hLK`
is replaced by its exact Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup`.
M004.002 in `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`,
lines 47–54 (file SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`),
has complete telescope `{G : Type u} [Group G] [TopologicalSpace G]
(K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup)` and
this exact body. The containment proof is unused by the abbreviation and
remains in the source object or constructor. The Mathlib construction
`Subgroup.subgroupOf` is the comap by the subgroup inclusion, at the approved
Mathlib pin `5ed2965256430c3649e86755f9576b54eca72435`.
The source abbreviation is discharged by this direct reuse, as authorized
by the task, rather than introducing a new public abbreviation.

Worker 198 prefixes the namespace, narrows imports to the published
abstract-extension and structural data, and expands only that abbreviation.
All data and instance proof bodies otherwise retain the source construction.
Source theorem commands M010.061–064 are omitted here.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
