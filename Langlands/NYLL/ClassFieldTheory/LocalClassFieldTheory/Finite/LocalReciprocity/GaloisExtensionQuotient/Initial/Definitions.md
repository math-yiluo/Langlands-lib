# Normal fixing subgroup and base-to-ambient quotient map

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M089.004 | `closedFixingSubgroup_normal` (60–65) | `closedFixingSubgroup_normal` |
| M089.006 | `baseFixingToAmbientQuotient` (77–84) | `baseFixingToAmbientQuotient` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

The source `Type` binders mean `Type 0` for both fields. All explicit/implicit and instance binders, the constructions and proof terms are retained. Prefix the source namespace by `Langlands.NYLL`; replace the two broad NYLL imports by the published closed-fixing-subgroup unit and Mathlib quotient groups; omit namespace openings not used in this extraction. The normality instance retains its source scope, with a qualified NYLL fixing subgroup as its head. It introduces no instance on a bare Mathlib fixing subgroup.



The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
