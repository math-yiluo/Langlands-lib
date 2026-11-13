# Intrinsic absolute Galois group, units and base

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M091.001 | `intrinsicAbsoluteGalois` (27–30) | `intrinsicAbsoluteGalois` |
| M091.002 | `intrinsicAbsoluteUnits` (32–37) | `intrinsicAbsoluteUnits` |
| M091.003 | `intrinsicAbstractBase` (39–45) | `intrinsicAbstractBase` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace and replace its broad quotient import by the two published data modules actually used. Omit unused namespace openings. The three abbreviation bodies and their explicit Type-zero field parameters and instances are unchanged.

The absolute group is the automorphism group of the chosen separable closure, its coefficient representation is the actual unit representation, and its distinguished base is the closed fixing subgroup of the bottom intermediate field.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
