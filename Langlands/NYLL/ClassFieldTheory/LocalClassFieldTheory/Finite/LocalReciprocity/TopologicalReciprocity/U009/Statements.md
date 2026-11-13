# Discrete commutator closure target

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M257.009 | `commutator_topologicalClosure_eq (private)` (353–359) | `Langlands.NYLL.PortInternal.M257.d009Statement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Replace the private source theorem by the contract-required stable `Langlands.NYLL.PortInternal.M257.d009Statement`, a Prop-valued definition with the exact proposition body and source Type-zero group telescope. Omit the proof and unrelated local-field section context, whose variables do not occur in the original theorem. Replace the broad imports by the focused Mathlib topological abelianization module.

The target says the commutator subgroup of an arbitrary discrete topological group is closed. It adds no local-field, finiteness or Galois hypothesis and makes no claim to topological reciprocity.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
