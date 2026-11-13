# Concrete unit carrier of the abstract extension representation

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M101.005 | `abstractExtensionFixedRepresentationUnitsEquiv` (116–128) | `abstractExtensionFixedRepresentationUnitsEquiv` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace and replace the broad imports by the relative fixed-field unit construction and the published fixed-representation carrier equivalence. Preserve the actual composite additive equivalence, including the inverse relative-unit equivalence. Keep source `Type 0` fields, the field and algebra instances, explicit `K L`, `hLK`, and normality witness in source order. As in the source, Lean omits `[IsGalois k Ω]` because neither the type nor the construction uses it. Expand `extensionSubgroup K L hLK` to its exact body `L.toSubgroup.subgroupOf K.toSubgroup` as permitted by the task; no new instance is introduced.

The domain is the actual quotient representation `CyclicCohomology.extensionFixedRepresentation` on ambient units. The codomain is the actual additive group of units of the scalar-extended upper fixed field. The source composite uses `ClassFormation.extensionFixedRepresentationEquiv`, then the inverse of `abstractRelativeFixedFieldUnitsEquivGaloisFixed`. It assumes no arbitrary carrier comparison or action compatibility theorem. The construction reuses the published `Langlands.NYLL.ClassFormation.extensionFixedRepresentationEquiv` by Lean name. This same-module carrier is used in the requested M101.009 action target.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.

Development check `596924c5-88bc-4c18-bd61-1b8fbb6be390` compiled both representation modules and confirmed that the M101.006 target returns `Prop`. Check `79feb3a3-6896-40da-b4b3-a77d9b6483ae` reconstructed both complete effective source telescopes and checked equality of the unapplied constants by `rfl`; it confirmed the actual composite construction and absence of an unused Galois instance. These development checks do not establish independent semantic acceptance or prove the compatibility target.
