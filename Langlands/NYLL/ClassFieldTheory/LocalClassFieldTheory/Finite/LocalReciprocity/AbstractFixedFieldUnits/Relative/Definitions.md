# Relative fixed-field units and ambient fixed coefficients

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M101.003 | `abstractRelativeFixedFieldUnitsEquivGaloisFixed` (93–101) | `abstractRelativeFixedFieldUnitsEquivGaloisFixed` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace and replace broad imports with the two focused sibling dependencies. Preserve the entire source construction, including the `change` command and the existing fixed-field unit equivalence. The source `Type 0` binders, field and algebra instances, explicit `K L` and `hLK` are unchanged. As in the original definition, Lean omits `[IsGalois k Ω]` because neither its type nor body uses that instance. No new instance is introduced.

The scalar-extended upper intermediate field has the same carrier and units as `abstractFixedField k Ω L`. The source body therefore uses `abstractFixedFieldUnitsEquivGaloisFixed k Ω L` directly after the same definitional change. It constructs an additive equivalence on the actual field units and fixed ambient coefficients; no arbitrary carrier or supplied equivalence replaces these objects.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
