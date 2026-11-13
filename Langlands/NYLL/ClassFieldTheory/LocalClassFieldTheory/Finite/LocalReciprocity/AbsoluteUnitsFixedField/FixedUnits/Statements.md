# Galois-fixed ambient unit targets

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M088.003 | `intermediateFieldUnitsToGaloisAmbient_apply` (47–53) | `intermediateFieldUnitsToGaloisAmbient_applyStatement` |
| M088.004 | `mem_galoisAmbientUnits_fixed_iff` (55–105) | `mem_galoisAmbientUnits_fixed_iffStatement` |
| M088.005 | `intermediateFieldUnitsToGaloisAmbient_range` (107–146) | `intermediateFieldUnitsToGaloisAmbient_rangeStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace; replace the three theorems by Prop-valued definitions with the `Statement` suffix and omit their proofs and simp attributes. Retain the full source Type-zero telescope, binder order and proposition bodies. The first target precedes the Galois hypothesis as in the source. Reuse the published initial ambient-unit definitions, closed fixing subgroup and ambient fixed additive subgroup. Imports and namespace openings are narrowed to these dependencies.

The targets describe evaluation of the actual unit inclusion, membership in the fixed subgroup in terms of the underlying field element, and equality of its range with that subgroup. They assert no proof and require no local-field or finite-dimensional hypotheses.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
