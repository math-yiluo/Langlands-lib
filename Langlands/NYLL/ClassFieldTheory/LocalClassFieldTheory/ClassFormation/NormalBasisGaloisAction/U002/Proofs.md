# Stable subgroup quotient action

Worker 277; focused proof for Task 5954 revision 2.

Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, is the original source.
The source is [`NormalBasisGaloisAction.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean>),
lines 58–65 (unit M145.002), declaration
`LocalClassFieldTheory.quotientActionOfSubgroupStable`.
The adapted theorem is
`Langlands.NYLL.LocalClassFieldTheory.quotientActionOfSubgroupStable`; its exact published target is
`Langlands.NYLL.LocalClassFieldTheory.quotientActionOfSubgroupStableStatement`.

The theorem retains independent universes `uG` and `uA`, explicit groups `G` and `A`, instances `Group G`, `CommGroup A`, `MulDistribMulAction G A`, an arbitrary subgroup `V`, and the explicit stability hypothesis `hstable`. Its type is exactly `quotientActionOfSubgroupStableStatement G A V hstable`. Although the statement definition does not use the value of `hstable` in its body, the proof uses it.

The proof constructs Mathlib's `MulAction.QuotientAction` record. If `a⁻¹ * b ∈ V`, stability gives `g • (a⁻¹ * b) ∈ V`. `MulDistribMulAction.smul_mul` and `map_inv` identify this element with `(g • a)⁻¹ * (g • b)`, giving the record's relation-preservation field. This is the original source proof route. The sole direct import is the published `NormalBasisGaloisAction.QuotientActionStatement` module; its Mathlib dependency is `Mathlib.GroupTheory.GroupAction.Quotient`. No action instance is installed by this theorem.

Modifications to the source: prefix the namespace with `Langlands.NYLL`, import
only the published target module, omit unrelated declarations and unused source
section variables, and state the theorem using the published proposition alias.
The implemented proof route is retained. The source copyright, author and
Apache-2.0 header is preserved; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
apply. No statement, definition or imported file is changed.

The readable source registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
Development and formal validation use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
This support lemma discharges no host class-formation, cup, transfer, Tate or
reciprocity target.
