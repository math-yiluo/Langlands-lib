# Concrete abstract fixed fields and their absolute Galois groups

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.001 | `abstractFixedField` (33–36) | `abstractFixedField` |
| M099.007 | `abstractSubgroupEquivGaloisGroup` (100–107) | `abstractSubgroupEquivGaloisGroup` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace; replace the source Mathlib/NYLL imports with the focused published closed-fixing-subgroup module, which imports the required InfiniteGalois API. All source data bodies, fields, universes and binders are unchanged. As in the source, `abstractFixedField` does not use the section’s `IsGalois` variable, so Lean omits that instance from its telescope. `abstractSubgroupEquivGaloisGroup` uses the instance in its proof term and retains it.

The construction is the actual `IntermediateField.fixedField H.toSubgroup`, and its subgroup isomorphism is the composite of `MulEquiv.subgroupCongr` using `InfiniteGalois.fixingSubgroup_fixedField` and `IntermediateField.fixingSubgroupEquiv`. No arbitrary field or assumed equivalence replaces the source objects.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
