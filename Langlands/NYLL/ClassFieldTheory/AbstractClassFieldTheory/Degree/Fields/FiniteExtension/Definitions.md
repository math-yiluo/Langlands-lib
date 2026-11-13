# NYLL M010: finite abstract-extension core data

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
| M010.065 | `FiniteAbstractExtension` | 552–563 | `FiniteAbstractExtension` |
| M010.066 | `FiniteAbstractExtension.subgroup` | 569–571 | `FiniteAbstractExtension.subgroup` |
| M010.067 | `FiniteAbstractExtension.quotient` | 573–575 | `FiniteAbstractExtension.quotient` |
| M010.068 | `FiniteAbstractExtension.ofInclusion` | 577–589 | `FiniteAbstractExtension.ofInclusion` |
| M010.071 | `FiniteAbstractExtension.IsUnramified` | 605–608 | `FiniteAbstractExtension.IsUnramified` |
| M010.072 | `FiniteAbstractExtension.IsTotallyRamified` | 610–613 | `FiniteAbstractExtension.IsTotallyRamified` |
| M010.077 | `FiniteAbstractExtension.quotientFinite` | 641–644 | `FiniteAbstractExtension.quotientFinite` |
| M010.078 | `FiniteAbstractExtension.representedQuotientFinite` | 646–652 | `FiniteAbstractExtension.representedQuotientFinite` |
| M010.085 | `FiniteAbstractExtension.degree` | 726–731 | `FiniteAbstractExtension.degree` |

The structure keeps explicit `(G : Type*) [Group G] [TopologicalSpace G]`,
extends the published `AbstractExtension G`, and adds exactly the source
`finiteQuotient : Finite (...)` field on its actual represented relative quotient.
The namespace definitions retain implicit `{G : Type u}` and its two instances,
and explicit `(E : FiniteAbstractExtension G)` when used. The source
`ofInclusion` does not depend on the section variable `E`: it retains explicit
`field`, `base`, `below` in that order and the instance binder
`[hfinite : Finite (base.toSubgroup ⧸ field.toSubgroup.subgroupOf base.toSubgroup)]`.
Its structure field assignments retain `hfinite` itself.

The two ramification predicates refer to the underlying abstract extension
with explicit `E` followed by explicit `D`. The two source finite instances
are retained with their source proof bodies: `quotientFinite` simplifies
the quotient/subgroup definitions using `E.finiteQuotient`;
`representedQuotientFinite` is `E.finiteQuotient` itself.
These are the source registrations, without additional conflicting instances.

`degree E : ℕ+` keeps the exact source body: locally install
`Nonempty E.quotient` using `QuotientGroup.mk 1`, then pair
`Nat.card E.quotient` with `Nat.card_pos`. This positive number is therefore
formed from the finite quotient stored in the extension, not a raw
infinite-as-zero index.

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

Worker 198 makes namespace, focused-import and abbreviation-expansion changes
only. Source universes, binder kinds, structure fields and proof terms are
retained; proof-only intervening theorem commands are omitted. M010.085
is placed in this core module because its only data dependency is the
stored finite quotient; it is independent of the later residue/inertia invariants.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
