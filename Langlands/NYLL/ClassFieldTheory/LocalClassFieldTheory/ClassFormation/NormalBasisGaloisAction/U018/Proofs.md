# Surjectivity of the integer-unit quotient map

Worker 277; focused proof for Task 5954 revision 2.

Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, is the original source.
The source is [`NormalBasisGaloisAction.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean>),
lines 273–276 (unit M145.018), declaration
`LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap_surjective`.
The adapted theorem is
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap_surjective`; its exact published target is
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap_surjectiveStatement`.

For arbitrary `L : Type u` with `Field L` and `ValuativeRel L` and arbitrary subgroup `V : Subgroup 𝒪[L]ˣ`, this proves exactly `chosenNormalBasisIntegerUnitsQuotientMap_surjectiveStatement L V`. There are no base-field, normal-basis, finite-extension or topology hypotheses. Commutativity of the unit group supplies subgroup normality for the group quotient.

The published quotient map is `QuotientGroup.mk' V`. Mathlib's `QuotientGroup.mk'_surjective V` supplies a representative for every quotient class, exactly as in the source. The sole direct import is the published `NormalBasisGaloisAction.IntegerUnitMapStatements` module, which imports `IntegerUnitMaps` and its Mathlib quotient-group and valuation-ring dependencies. The proof does not depend on another new proof in this task.

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
