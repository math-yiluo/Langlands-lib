# Finite extension and tower unit Tate cardinality targets

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteExtensionClassFieldAxiom.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M158.002 | `finiteExtensionUnits_tate_card_of_generator` (54–175) | `finiteExtensionUnits_tate_card_of_generatorStatement` |
| M158.003 | `finiteTowerUnits_tate_card_of_generator` (177–224) | `finiteTowerUnits_tate_card_of_generatorStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace and replace theorem commands by Prop-valued Statement definitions, omitting proofs and retaining every source hypothesis and binder order. Reuse the sibling exact source structure and Mathlib local-field predicates. No local-field structure on the upper field is assumed.



The sibling structure is inferred in Prop by Lean, so the exact source results are valid proposition bodies without a Nonempty wrapper. Both generator hypotheses are retained even though they occur only in the omitted proofs; their unused-variable warnings are expected.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
