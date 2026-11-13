# NYLL M012: extension inertia and restriction data

This module adapts M012.002, M012.003 and M012.007 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean`.
The file SHA-256 is
`a0b7ac8afcc55cad383a16e6dfe093e147770a7e8f5d21c3f8843744b57b7061`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The adapted names have prefix `Langlands.NYLL.ClassFormation.DegreeData`;
the original names have prefix `ClassFormation.DegreeData`.

| Unit | Source lines | Original suffix | Adapted suffix |
| --- | --- | --- | --- |
| M012.002 | 58–60 | `extensionInertiaWithin` | `extensionInertiaWithin` |
| M012.003 | 65–70 | `extensionInertiaWithin_normal` | `extensionInertiaWithin_normal` |
| M012.007 | 107–113 | `extensionRestriction` | `extensionRestriction` |

All three declarations retain the source universe `u`, implicit `G : Type u`,
then `[Group G]` and `[TopologicalSpace G]`. Their explicit binders are
`D : DegreeData G`, `K L : ClosedSubgroup G`, and
`hLK : L.toSubgroup ≤ K.toSubgroup`, in that order. The normality instance
and restriction map then take the instance binder
`[hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]`.
The containment proof remains an explicit parameter even though the subgroup
construction's body does not use it. No finiteness, profiniteness,
topological-group or finite-residue assumption is added.

The source abbreviation `CyclicCohomology.extensionSubgroup K L hLK`
(M004.002, `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`,
lines 47–54; file SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`)
is exactly `L.toSubgroup.subgroupOf K.toSubgroup`. This module uses that
Mathlib expression directly at every occurrence, as authorized by Task 5820.
It introduces no replacement abbreviation and does not depend on the pending
port of M004.002. This expands an abbreviation without changing the object
or any binder. The imported published `fieldInertiaWithin` is the actual
kernel of the restricted degree map.

`extensionInertiaWithin` is the intersection of that extension subgroup with
`D.fieldInertiaWithin K`, as a subgroup of `K.toSubgroup`. Its normality
instance retains the source proof: unfold this intersection and use the
normality of each factor. The source global instance scope is retained for
this specific new subgroup family; no general Mathlib instance is duplicated.
`extensionRestriction` retains the source `QuotientGroup.map` construction
induced by `MonoidHom.id K.toSubgroup`, with containment proof `inf_le_left`.
Its source is the actual quotient by extension inertia, and its target is
the actual quotient by the extension subgroup. Both use the retained
normality instances.

Worker 191 prefixes the namespace, expands only the source abbreviation
described above, and replaces the full `Degree.Frobenius` import with
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`.
The unused `open CyclicCohomology` is omitted. The source noncomputable
section, extracted docstrings, binder kinds, bodies and normality proof are
otherwise retained. Intervening normalized-degree declarations and all other
source commands are omitted because none of these three units uses them.

This is a data construction unit. It supplies no theorem target proof,
Frobenius lifting theorem, normalized-degree construction or host reciprocity
comparison.

The original copyright, author and Apache-2.0 header is retained.
`licenses/NYLL/LICENSE` has SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`;
`licenses/NYLL/NOTICE` has SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
