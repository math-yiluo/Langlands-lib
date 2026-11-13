# Scalar extension of abstract fixed fields

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.009 | `abstractRelativeFixedField` (116–122) | `abstractRelativeFixedField` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace by `Langlands.NYLL` and reduce imports to the sibling initial definitions. Preserve the actual `IntermediateField.extendScalars` construction, both source `Type 0` field binders, field and algebra instances, implicit `{K L}` binders, and explicit `hLK`. The source abbreviation has no `IsGalois k Ω` parameter: it is not used in its type or body, since M099.006 explicitly omits it. No instance is introduced.

The source argument `abstractFixedField_le k Ω hLK` (M099.006, lines 94–98) is discharged by the existing Mathlib theorem `IntermediateField.fixedField_le hLK`. The original M099.006 proof is exactly that named theorem, and `abstractFixedField` is the actual Mathlib fixed field; the replacement is definitionally the source proof term. A focused full-telescope check verifies the Mathlib theorem at the source M099.006 type without a Galois hypothesis, and checks this abbreviation at the complete source M099.009 type. This change introduces no source theorem proof or alternative intermediate field. The M099.006 proposition remains independently recorded by `abstractFixedField_leStatement` in the initial statement pair.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
