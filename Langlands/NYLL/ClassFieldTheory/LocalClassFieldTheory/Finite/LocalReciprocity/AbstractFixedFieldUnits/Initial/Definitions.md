# Fixed-field units and Galois-fixed ambient coefficients

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M101.001 | `abstractFixedFieldUnitsEquivGaloisFixed` (38–79) | `abstractFixedFieldUnitsEquivGaloisFixed` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace by `Langlands.NYLL`; replace the broad source imports by the three focused Library inputs; omit namespace openings not used by this unit. Retain the exact source equivalence fields and proof bodies. The source declares `k Ω : Type 0`, with explicit field and algebra instances; the section `IsGalois` instance is unused and therefore omitted by Lean, as in the original. No additional global instance is introduced.

The forward map is inclusion of actual fixed-field units in `Ωˣ`, written additively. The inverse proves that the ambient unit lies in the fixed field and constructs its nonzero fixed-field unit with `Units.mk0`. Its inverse laws and additive law are the source proof terms. This is a constructed additive equivalence, with no finiteness assumption on the closed subgroup.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
