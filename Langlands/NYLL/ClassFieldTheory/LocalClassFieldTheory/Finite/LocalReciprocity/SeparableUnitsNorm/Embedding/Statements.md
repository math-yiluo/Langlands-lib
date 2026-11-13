# Norm invariance under embedded field realization

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M096.012 | `normUnits_embeddedExtensionAlgEquiv` (356–364) | `normUnits_embeddedExtensionAlgEquivStatement` |
| M096.013 | `localNormSubgroup_fieldRange_eq` (366–385) | `localNormSubgroup_fieldRange_eqStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace; replace the source theorems by Prop-valued Statement definitions and omit proofs. Retain source section contexts (36–37, 344–346), source omissions, proposition bodies and binder order. The local finite-dimensional and Galois instances of lines 348–354 are unused by these omitted-hypothesis statements and are not exported. Import the published norm image and its normUnits dependency, and the focused Mathlib field-range equivalence API. Omit unused namespace openings.

Both targets concern an arbitrary field embedding: no finite-dimensionality or Galois hypotheses remain in their actual telescopes. The first compares the ordinary norm of a mapped unit with its original norm, and the second compares the two actual norm image subgroups.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
