# Concrete Galois action on abstract fixed-field units

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M101.007 | `abstractExtensionQuotientEquivGaloisGroup_mk_apply_val` (149–202) | `abstractExtensionQuotientEquivGaloisGroup_mk_apply_valStatement` |
| M101.008 | `relativeCosetAction_abstractRelativeFixedFieldUnit_val` (204–233) | `relativeCosetAction_abstractRelativeFixedFieldUnit_valStatement` |
| M101.009 | `abstractExtensionFixedRepresentationUnitsEquiv_action` (235–274) | `abstractExtensionFixedRepresentationUnitsEquiv_actionStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace with `Langlands.NYLL` and replace each
theorem by a Prop-valued `def` with the `Statement` suffix, preserving its
entire proposition and explicit argument order. Omit each proof. Reduce
imports to the concrete quotient/Galois equivalences, the published
unit-carrier equivalence and the published relative coset action definitions.
Omit unused namespace openings. Retain the source
section variables from line 36: explicit Type-0 fields `k Ω`, field and algebra
instances, and `[IsGalois k Ω]`, which is used by the actual quotient/Galois
equivalence in each proposition. After `K L`, `hLK` and `hnormal`, M101.007 has
`σ` then `x`; M101.008 has `x` then `q`; M101.009 has `q` then `x`.
All these binders remain explicit. Each result retains `letI := hnormal`.
Expand the source relative subgroup abbreviation to its exact Mathlib body
`L.toSubgroup.subgroupOf K.toSubgroup` (M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`). No global
instance is introduced.

M101.007 states that the concrete relative Galois automorphism
associated to the quotient class of `σ : K.toSubgroup` sends `x` to the same
ambient value as `σ.1`. Both sides are compared in `Ω`, with the actual
quotient map `QuotientGroup.mk'` and constructed
`abstractExtensionQuotientEquivGaloisGroup`.

M101.008 compares the ambient values of the abstract coset action on the
constructed fixed coefficient of an upper-field unit and of the actual
`Rep.ofAlgebraAutOnUnits` action of the associated relative Galois
automorphism. It uses the actual `relativeCosetAction`,
`abstractRelativeFixedFieldUnitsEquivGaloisFixed` and quotient/Galois
equivalence, with the same source unit `x` and quotient element `q`.

M101.009 says that the constructed additive carrier equivalence
`abstractExtensionFixedRepresentationUnitsEquiv` intertwines the actual
descended quotient representation with the actual relative Galois action on
upper-field units, reindexed through the concrete quotient/Galois
equivalence. There is no assumed carrier comparison or action law replacing
any of these objects. These are three proposition definitions; no proof of
any target is supplied.

The whole original M101 file has SHA-256 `9a2d82d81f9f00269a7f9904e005ab931bbde64ea62cbe8fe7327d7b31a017f1`.
Its theorem signatures are lines 151–162, 206–224 and 237–253. The source
proof of M101.008 uses M101.007, and the proof of M101.009 uses M101.008; the
targets themselves are independent definitions. Private development probes
compare each unapplied target with its complete source-telescope proposition
by `rfl`, and each target receives a focused `Prop` inspection. These
development checks are separate from semantic review and proof acceptance.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
