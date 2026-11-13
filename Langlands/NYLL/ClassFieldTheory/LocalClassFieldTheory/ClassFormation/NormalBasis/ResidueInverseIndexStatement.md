# Evaluation target for inverse-index residue coordinates

Worker 197; NYLL statement-layer adaptation for Task 5874.

The pinned original is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, source file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean`. The readable original is [NormalBasis.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean>). Registration `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; supplement registration `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Every source name in the following table has prefix `LocalClassFieldTheory.`; every adapted name has prefix `Langlands.NYLL.LocalClassFieldTheory.`.

| Source declaration | Exact source lines | Adapted declaration |
| --- | --- | --- |
| `chosenNormalBasisPiResidueInverseIndexAddEquiv_apply` | 356–361 | `chosenNormalBasisPiResidueInverseIndexAddEquiv_applyStatement` |

The source unit is M152.020. The shared universe, explicit `K`, `L`, instance-implicit `Field K`, `ValuativeRel K`, `Field L`, `Algebra K L`, then `TopologicalSpace K`, `IsNonarchimedeanLocalField K`, explicit coordinate function `f`, and explicit Galois index `σ` are retained in source order. The source omits `FiniteDimensional K L` and `IsGalois K L` at lines 352–354; its two topology/local-field instances are still retained by the theorem command. They are explicitly bound here despite the algebraic equality formula. The target computes the actual equivalence at the inverse Galois element.

Modifications: prefix the source namespace with `Langlands.NYLL`; reduce imports to the named Mathlib or Library dependency modules; omit unrelated source declarations and unused namespace openings. Replace each source theorem by a `def` whose result is `Prop`, append `Statement` to its name, and retain the source target expression and complete source telescope; the original proof and theorem attributes are omitted. Any source section instance not inferred from the Prop body is bound explicitly. No theorem proof is supplied. The original copyright, author and Apache-2.0 header is retained. The published `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. No patch10 compatibility edits are used.

Checks use environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) through `lean_check`. Compilation does not establish independent mathematical acceptance. This unit makes no host reciprocity or class-formation claim.
