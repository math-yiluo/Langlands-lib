# Stable internal names for intrinsic transport data

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M097.001 | `G (private)` (41–42) | `Langlands.NYLL.PortInternal.M097.d001` |
| M097.002 | `A (private)` (44–45) | `Langlands.NYLL.PortInternal.M097.d002` |
| M097.003 | `B (private)` (47–48) | `Langlands.NYLL.PortInternal.M097.d003` |
| M097.004 | `intrinsicAbsoluteGaloisT2 (private instance)` (50–51) | `Langlands.NYLL.PortInternal.M097.d004` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

The contract requires stable names for private source commands. Move them to `Langlands.NYLL.PortInternal.M097` and rename G/A/B/the instance as d001/d002/d003/d004, updating references to G as d001. Retain each abbreviation body, the source Type-zero field parameter and the complete `krullTopology_t2` instance term. Retain the source instance scope (private global instance becomes a named global instance under the stable internal namespace); no new topology is defined. Omit unused broad imports and namespace openings, opening the published LocalClassFieldTheory namespace instead. Source section parameters are at lines 38–39; unused ones are omitted by Lean exactly as in the source.

The three abbreviations reuse the published intrinsic data. The final declaration certifies the existing Krull topology is T2; it creates no competing topology or algebra structure.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
