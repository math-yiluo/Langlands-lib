# NYLL M010: abstract-extension and cardinal data

This module extracts six data commands from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, source
lines 219–268, at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Its SHA-256 is `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

All names below have prefix `Langlands.NYLL.ClassFormation.DegreeData`.

| Unit | Original name after `ClassFormation.DegreeData.` | Source lines | Adapted name after the public prefix |
| --- | --- | --- | --- |
| M010.028 | `AbstractExtension` | 219–229 | `AbstractExtension` |
| M010.029 | `AbstractExtension.subgroup` | 233–237 | `AbstractExtension.subgroup` |
| M010.030 | `AbstractExtension.quotient` | 239–241 | `AbstractExtension.quotient` |
| M010.031 | `AbstractExtension.degreeCardinal` | 243–246 | `AbstractExtension.degreeCardinal` |
| M010.033 | `AbstractExtension.relativeResidueDegreeCardinal` | 253–258 | `AbstractExtension.relativeResidueDegreeCardinal` |
| M010.034 | `AbstractExtension.relativeRamificationIndexCardinal` | 260–268 | `AbstractExtension.relativeRamificationIndexCardinal` |

The source `AbstractExtension (G : Type*) [Group G] [TopologicalSpace G]`
keeps its explicit group parameter and arbitrary universe. It has exactly
two closed subgroups, `field` and `base`, and the intrinsic proof
`below : field.toSubgroup ≤ base.toSubgroup`. This contravariant field
containment is retained in the object. No normality, profiniteness,
finiteness or topological-group hypothesis is introduced. The extension
object does not carry a degree datum.

For the five remaining declarations, source section parameters are implicit
`G : Type u` with `[Group G]` and `[TopologicalSpace G]`; `E` is explicit.
The last two then have explicit `D : DegreeData G`, in that order.
`subgroup E` is the actual extension subgroup inside `E.base.toSubgroup`.
`quotient E : Type u` is its actual left-coset type, formed without any
normality assumption. `degreeCardinal E` uses the published source
`relativeIndexCardinal E.below`, hence preserves its full cardinal value,
including infinity, in universe `u`.

The residue cardinal is the relative index cardinal of the two subgroup
images under `D.degree.toMonoidHom`, using `Subgroup.map_mono` on `E.below`.
Its quotient lies in the Type-zero `ZHatMul` model. The ramification
cardinal is the relative index cardinal of the intersections of the two
subgroups with the actual degree kernel, with inclusion proved by
`inf_le_inf E.below le_rfl`; this cardinal remains in universe `u`.
All three cardinal constructions retain their source bodies, and no
natural-valued index or infinite-as-zero convention is substituted.

The only construction substitution is in M010.029. The original calls
`CyclicCohomology.extensionSubgroup E.base E.field E.below`.
M004.002 at source
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54,
defines that abbreviation with the complete telescope
`{G : Type u} [Group G] [TopologicalSpace G] (K L : ClosedSubgroup G)
(_hLK : L.toSubgroup ≤ K.toSubgroup)` and exact body
`L.toSubgroup.subgroupOf K.toSubgroup`. Its file SHA-256 is
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
Here `subgroup E` directly reuses the published Mathlib declaration
`Subgroup.subgroupOf`, with body
`E.field.toSubgroup.subgroupOf E.base.toSubgroup`.
Mathlib defines this construction as the comap by the subgroup inclusion
in `Mathlib/Algebra/Group/Subgroup/Map.lean`, lines 282–285, at the approved
Mathlib pin `5ed2965256430c3649e86755f9576b54eca72435`.
The source inclusion proof is unused by its abbreviation and remains
stored as `E.below` in the extension. Thus neither a different subgroup
nor an additional hypothesis replaces the source one.

A private focused compatibility check retains the entire M004.002 source
telescope and identifies its body with `Subgroup.subgroupOf` by `rfl`.
It also identifies the whole dependent function `fun E => E.subgroup`
with the original abbreviation applied to `E.base`, `E.field` and
`E.below`, before application, by `rfl`. These checks establish this
specific reuse without importing the representation and Tate-cohomology
parts of the original module. No new public copy of `extensionSubgroup`
is supplied. Its other source consumers and the separately routed
M004.003–005 remain separate obligations.

Worker 120 prefixes the namespace, performs only that abbreviation
substitution, omits the intervening theorem M010.032 and later theorem
bodies, and narrows imports to the published initial `Fields.Definitions`.
The latter reuses the published NYLL closure model and cardinal-index data.
The source `noncomputable section`, explicit noncomputable modifiers,
structure fields, binder kinds and universes are retained. The original
`open CyclicCohomology` becomes unused and is omitted. No new instance is
declared. No cardinal identity, tower, ramification predicate, theorem
proof, host class-formation or reciprocity assertion is supplied.

The original author and copyright header is retained. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
See retained Apache-2.0 files `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
