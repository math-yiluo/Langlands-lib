# Compatibility of the two fixed-unit carrier equivalences

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M101.006 | `abstractRelativeUnitsEquiv_extensionUnitsEquiv` (130–147) | `abstractRelativeUnitsEquiv_extensionUnitsEquivStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace and convert the source theorem to a Prop-valued `Statement` definition, retaining the exact equality, source binder order and `omit [IsGalois k Ω]`. Remove the theorem-only `simp` attribute and omit the proof. Expand the source relative subgroup abbreviation to `L.toSubgroup.subgroupOf K.toSubgroup`, its exact Mathlib body; retain the supplied normality witness. Reduce imports to the companion carrier construction.

For each vector of the actual extension fixed representation, the proposition compares the two constructed routes to the ambient fixed subgroup. Both the normality argument and the vector remain explicit, with source `Type 0` fields and no Galois instance. This is a separate target, without its source proof. The carrier equivalence is the published cross-module construction, reused by Lean name; the companion definition supplies the concrete unit carrier.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.

Development check `596924c5-88bc-4c18-bd61-1b8fbb6be390` compiled both representation modules and confirmed that the M101.006 target returns `Prop`. Check `79feb3a3-6896-40da-b4b3-a77d9b6483ae` reconstructed both complete effective source telescopes and checked equality of the unapplied constants by `rfl`; it confirmed the actual composite construction and absence of an unused Galois instance. These development checks do not establish independent semantic acceptance or prove the compatibility target.
