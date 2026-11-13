# Evaluation of the relative fixed-field unit equivalence

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M101.004 | `abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe` (103–114) | `abstractRelativeFixedFieldUnitsEquivGaloisFixed_coeStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace; replace the source theorem by a Prop-valued `Statement` definition with the exact source equality and binder order. Retain the source `omit [IsGalois k Ω]`; remove the theorem-only `simp` attribute and omit the proof. Imports are reduced to the relative fixed-field unit definition.

For every explicit relative subgroup pair `K L`, inclusion witness `hLK`, and additive upper-field unit `x`, the target identifies the underlying ambient unit of the constructed equivalence with the original `intermediateFieldUnitsToGaloisAmbient` map. Its universe is the source `Type 0`, and it requires no Galois instance. This is the evaluation statement needed by later action transport, with its proof reserved for a separate task.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
