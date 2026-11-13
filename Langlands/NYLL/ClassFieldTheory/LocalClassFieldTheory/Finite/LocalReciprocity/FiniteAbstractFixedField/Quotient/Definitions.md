# Relative fixed-field quotient homomorphism

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.013 | `abstractRelativeToAmbientQuotient` (194–208) | `abstractRelativeToAmbientQuotient` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace with `Langlands.NYLL` and replace the broad source imports by the published M099.011 proof module, which imports the relative fixed-field data and the InfiniteGalois and quotient APIs. Omit unused namespace openings. Preserve the complete source telescope, including explicit `k Ω : Type` (both Type 0), `[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, explicit `K L`, `hLK` and `hnormal`. The result type retains the original `letI` normality witness with the concrete type annotation explained below. The source data body, including its local instance and proof term, is unchanged except for the subgroup spelling explained below.

The original `CyclicCohomology.extensionSubgroup K L hLK` is written as its exact Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup`, following the published relative definitions and targets. This abbreviation is M004.002, `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`; it ignores the inclusion proof in its body. No subgroup is replaced by an abstract parameter.

The construction first installs the published theorem `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal` as a local normality instance. It composes the actual `abstractSubgroupEquivGaloisGroup k Ω K` homomorphism with `QuotientGroup.mk'` for the fixing subgroup of `abstractRelativeFixedField k Ω hLK`. Thus it is the source restriction-and-quotient map on the actual fixed fields. The normality theorem is used by Lean name through its published module; no source proof is inlined here and no global instance is added.

The result-type `letI` has the explicit type annotation `(abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal`. The published proof theorem has the definitionally equal type `abstractRelativeFixingSubgroup_normalStatement ...`; without the annotation, Lean does not register that proposition alias as the needed class. The annotation restores the source local instance with precisely the same proof term and no change to the quotient or homomorphism.

The whole original M099 file has SHA-256 `d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`. Its section variables are on line 31; the declaration is on lines 196–208, preceded by its docstring on lines 194–195. A private development comparison checks equality of the unapplied adapted constant with the complete source construction by `rfl`, including its full telescope. The independent compilation and semantic review requirements remain separate.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
