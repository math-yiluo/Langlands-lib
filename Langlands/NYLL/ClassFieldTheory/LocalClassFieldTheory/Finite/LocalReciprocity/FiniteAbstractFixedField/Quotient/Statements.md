# Kernel and surjectivity of the relative quotient homomorphism

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.014 | `abstractRelativeToAmbientQuotient_ker` (210–234) | `abstractRelativeToAmbientQuotient_kerStatement` |
| M099.015 | `abstractRelativeToAmbientQuotient_surjective` (236–254) | `abstractRelativeToAmbientQuotient_surjectiveStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace with `Langlands.NYLL`; replace each source theorem by a Prop-valued `def` with the `Statement` suffix, retaining its complete proposition and binder order. Omit its proof. The source variables are explicit `k Ω : Type` (both Type 0), `[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, followed by explicit `K L`, `hLK` and `hnormal`. Both proposition bodies preserve the source `letI := abstractRelativeFixingSubgroup_normal ...` in the result type. Imports are reduced to the sibling quotient definition; unused source namespace openings are omitted.

As in the quotient data and published relative targets, write the original `CyclicCohomology.extensionSubgroup K L hLK` as its exact Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` (M004.002, `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`). Each result-type `letI` also has the concrete type annotation `(abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal`: the published normality theorem returns a definitionally equal proposition alias, which an untyped `letI` does not register as a class. This annotation retains the same local instance proof term and source proposition.

M099.014 states that the kernel of the actual `abstractRelativeToAmbientQuotient k Ω K L hLK hnormal` is the exact relative subgroup `L.toSubgroup.subgroupOf K.toSubgroup`. M099.015 states that the same quotient homomorphism is surjective. The normality instance is local to each proposition, exactly as in the source; these definitions assert no proof of either proposition and register no global instance. Proofs of these targets are separate work.

The whole original M099 file has SHA-256 `d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`; the section variables are on line 31. The kernel signature is lines 212–220 and its proof lines 221–234. The surjectivity signature is lines 237–245 and its proof lines 246–254. The paired Lean file keeps each entire signature as a proposition, including the `letI` expression before the equality or surjectivity body. Private development comparisons check equality of both unapplied targets with complete source-telescope proposition definitions by `rfl`. Each target also receives a focused `Prop` inspection.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
