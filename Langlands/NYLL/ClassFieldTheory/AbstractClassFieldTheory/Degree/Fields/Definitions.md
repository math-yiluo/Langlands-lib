# NYLL M010: degree datum and initial field and inertia data

This data unit adapts commands M010.001–003, .006, .008, .010, .012, .014–015
and .017–018 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The original file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

All names in the table have prefix `Langlands.NYLL.ClassFormation`. The
original declarations' types and construction bodies are retained.

| Unit | Original lines and name | Adapted name |
| --- | --- | --- |
| M010.001 | 32–34, `ClassFormation.ZHatMul` | `ZHatMul` |
| M010.002 | 36–44, `ClassFormation.DegreeData` | `DegreeData` |
| M010.003 | 48–52, `ClassFormation.baseField` | `baseField` |
| M010.006 | 67–72, `ClassFormation.DegreeData.inertia` | `DegreeData.inertia` |
| M010.008 | 80–85, `ClassFormation.DegreeData.restrictedDegree` | `DegreeData.restrictedDegree` |
| M010.010 | 92–94, `ClassFormation.DegreeData.fieldImage` | `DegreeData.fieldImage` |
| M010.012 | 106–108, `ClassFormation.DegreeData.fieldInertia` | `DegreeData.fieldInertia` |
| M010.014 | 116–119, `ClassFormation.DegreeData.fieldInertiaWithin` | `DegreeData.fieldInertiaWithin` |
| M010.015 | 121–125, `ClassFormation.DegreeData.fieldInertiaWithin_normal` | `DegreeData.fieldInertiaWithin_normal` |
| M010.017 | 133–138, `ClassFormation.DegreeData.residueDegreeCardinal` | `DegreeData.residueDegreeCardinal` |
| M010.018 | 140–142, `ClassFormation.DegreeData.residueQuotient` | `DegreeData.residueQuotient` |

`ZHatMul : Type 0` is the multiplicative presentation of the published source
closure-model `ZHat`: its multiplication is addition in the ring. `DegreeData`
takes an arbitrary group `G : Type*` with a topology. It consists of an actual
continuous monoid homomorphism `degree : G →ₜ* ZHatMul` and a proof that this
map is surjective. It neither assumes that `G` is profinite nor adds a
topological-group instance. Surjectivity is the intrinsic field of the source
datum, rather than a newly postulated axiom or theorem about every group.

For the remaining declarations the source section has implicit `G : Type u`,
`[Group G]` and `[TopologicalSpace G]`, in that order. `baseField` instead has
explicit `G` followed by these same instances and is the closed top subgroup.
Each `DegreeData` method takes explicit `D : DegreeData G`; methods for a
field then take explicit `K : ClosedSubgroup G`. Inertia is the kernel of the
actual degree homomorphism, with closedness proved by continuity and the
Hausdorff structure on the actual target. `restrictedDegree` composes the map
with the underlying subgroup inclusion; `fieldImage` is its actual range.
`fieldInertia` intersects the closed subgroup with ambient inertia, while
`fieldInertiaWithin` is the restricted map's kernel as a subgroup of `K`.
The normality instance retains its source global registration on this specific
new subgroup family, using Mathlib's kernel-normality instance.

The two residue objects retain the source's actual quotient of the top subgroup
of `ZHatMul` by the degree image. `residueDegreeCardinal` uses the published
`relativeIndexCardinal`, which is `Cardinal.mk` of that coset type; it does not
collapse an infinite cardinal to a natural-valued index. `residueQuotient` is
the Type-zero coset type itself. No finite-quotient or subgroup-normality
hypothesis is added. These definitions give the data; their equality as a
named statement remains a later source unit.

Worker 120 prefixes the namespace with `Langlands.NYLL`, retains the source
noncomputable section and all extracted docstrings, and omits intervening
theorems and the unused opening of `CyclicCohomology`. The source's Mathlib
quotient-group import is retained. The NYLL imports of IntegralRepUniverse,
NormKernelVanishing, all of Indices and all of ProfiniteInteger are replaced by
the published focused M006.010–011 cardinal data and M008.001–018 closure data.
No extracted body uses a representation, Tate theorem, M006 index law, or
M008/M009 theorem. Focused compilation checks that this smaller import set
suffices. The source structures and proof fields themselves are preserved.

This unit proves no named field, index or inertia theorem; it does not construct
a degree datum for an arithmetic field, supply later finite-residue field or
extension structures, normalize a degree, or assert local reciprocity. No
comparison with host class-formation or profinite-integer models is claimed.

The original copyright, Apache-2.0 and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
