# Base fixing subgroup and quotient surjectivity targets

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M089.001 | `closedFixingSubgroup_bot_eq_baseField` (31–39) | `closedFixingSubgroup_bot_eq_baseFieldStatement` |
| M089.002 | `fixingSubgroupLeBase` (41–47) | `fixingSubgroupLeBaseStatement` |
| M089.008 | `baseFixingToAmbientQuotient_surjective` (101–115) | `baseFixingToAmbientQuotient_surjectiveStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace; replace each source theorem by a Prop-valued definition with `Statement` suffix, retaining the complete source telescope, binder order and proposition body. Source proofs are omitted. Imports are reduced to the published NYLL base field and the sibling initial quotient definitions. No theorem proof is asserted here.

For fields `K Ω : Type 0` in the source Galois context, the targets say that the bottom-field fixing group is the full distinguished abstract base, each intermediate-field fixing subgroup lies in that group, and the source base-to-ambient quotient homomorphism is surjective. These are separate targets; the file does not assert a proof of any target.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
