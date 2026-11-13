# Relation preservation for a stable-subgroup quotient

Worker 197; NYLL statement-layer adaptation for Task 5874.

The pinned original is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, source file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`. The readable original is [NormalBasisGaloisAction.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean>). Registration `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; supplement registration `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Every source name in the following table has prefix `LocalClassFieldTheory.`; every adapted name has prefix `Langlands.NYLL.LocalClassFieldTheory.`.

| Source declaration | Exact source lines | Adapted declaration |
| --- | --- | --- |
| `quotientActionOfSubgroupStable` | 58–65 | `quotientActionOfSubgroupStableStatement` |

The source unit is M145.002. Its complete telescope has independent universes `uG` and `uA`; explicit `G`, `A`; instance-implicit `Group G`, `CommGroup A`, `MulDistribMulAction G A`; explicit `V`; and explicit `hstable`. The last binder is retained even though the target proposition does not depend on its value. Mathlib's `MulAction.QuotientAction` is a Prop-valued class, so this is a proposition target, not a replacement action instance. The target is exactly `MulAction.QuotientAction G V`. No global or local instance is installed.

The source proof will belong to a separate proof task after target publication. Mathlib's quotient action on `A ⧸ V` requires this relation-preservation class and does not itself establish it from `hstable`.

Modifications: prefix the source namespace with `Langlands.NYLL`; reduce imports to the named Mathlib or published Library modules; omit unrelated source declarations and unused namespace openings. Replace each source theorem by a `def` whose result is `Prop`, append `Statement` to its name, and retain the source target expression and binders; the original proof and theorem attributes are omitted. No theorem proof is supplied. The original copyright, author and Apache-2.0 header is retained. The published `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. No patch10 compatibility edits are used.

Checks use environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) through `lean_check`. Compilation does not establish independent mathematical acceptance. This unit makes no host reciprocity or class-formation claim.

Development validation: terminal `lean_check` record `acc511b4-84d5-443a-9405-3ac143af7e27` compiled both modules with no errors. Its exact declaration inspection for `quotientActionOfSubgroupStableStatement` reported `statement_returns_prop: true`, universe parameters `uG`, `uA`. The sole warning records the deliberately retained explicit `hstable` binder.
