# Restrict an action to an invariant subgroup

Worker 197; NYLL statement-layer adaptation for Task 5874.

The pinned original is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, source file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`. The readable original is [NormalBasisGaloisAction.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean>). Registration `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; supplement registration `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Every source name in the following table has prefix `LocalClassFieldTheory.`; every adapted name has prefix `Langlands.NYLL.LocalClassFieldTheory.`.

| Source declaration | Exact source lines | Adapted declaration |
| --- | --- | --- |
| `subgroupMulDistribMulActionOfStable` | 33–54 | `subgroupMulDistribMulActionOfStable` |

The source unit is M145.001. The independent universes `uG` and `uA`, explicit types `G` and `A`, instance-implicit `Group G`, `CommGroup A`, `MulDistribMulAction G A`, explicit subgroup `V` and explicit stability proof `hstable` are retained in that order. The construction acts by the ambient scalar action on the underlying element and proves its group-action and multiplicativity fields by subtype extensionality, exactly as in the source. The source `@[implicit_reducible]` attribute is retained. It is a data declaration, not an instance declaration.

Mathlib's generic quotient action and the fixed-point or conjugation subgroup actions do not supply this exact construction for an arbitrary explicitly supplied stable subgroup. The subtype and action laws themselves are reused from Mathlib.

Modifications: prefix the source namespace with `Langlands.NYLL`; reduce imports to the named Mathlib or published Library modules; omit unrelated source declarations and unused namespace openings. Keep the data expressions and constructor proof fields. The original copyright, author and Apache-2.0 header is retained. The published `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. No patch10 compatibility edits are used.

Checks use environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) through `lean_check`. Compilation does not establish independent mathematical acceptance. This unit makes no host reciprocity or class-formation claim.

Development validation: terminal `lean_check` record `acc511b4-84d5-443a-9405-3ac143af7e27` compiled both modules with no errors. Its exact declaration inspection for `quotientActionOfSubgroupStableStatement` reported `statement_returns_prop: true`, universe parameters `uG`, `uA`. The sole warning records the deliberately retained explicit `hstable` binder.
