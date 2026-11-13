# Abstract fixed-field recovery, order and evaluation targets

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.002 | `closedFixingSubgroup_abstractFixedField_eq` (38–46) | `closedFixingSubgroup_abstractFixedField_eqStatement` |
| M099.006 | `abstractFixedField_le` (92–98) | `abstractFixedField_leStatement` |
| M099.008 | `abstractSubgroupEquivGaloisGroup_apply` (109–114) | `abstractSubgroupEquivGaloisGroup_applyStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace and replace source theorems by Prop-valued `Statement` definitions, preserving their propositions and telescope order, including the source `omit [IsGalois k Ω]` on M099.006. Remove the source `simp` attribute because these are proposition definitions. Imports are reduced to the sibling initial definitions. Proofs are separate work.

The first target recovers the closed subgroup after taking its fixed field; the second reverses subgroup inclusion on fixed fields; the third specifies the pointwise action of the actual subgroup/Galois equivalence. The independent implicit `{K L}` subgroup binders and explicit `hLK` proof remain unchanged.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
