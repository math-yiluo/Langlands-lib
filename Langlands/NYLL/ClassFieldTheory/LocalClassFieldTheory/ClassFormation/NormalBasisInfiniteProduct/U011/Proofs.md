# Successor equation for normal-basis correction products

Worker 277; focused proof for Task 5954 revision 2.

Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, is the original source.
The source is [`NormalBasisInfiniteProduct.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean>),
lines 269–273 (unit M150.011), declaration
`LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_succ`.
The adapted theorem is
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_succ`; its exact published target is
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_succStatement`.

For arbitrary `L : Type u` with `Field L` and `ValuativeRel L`, any sequence `z : Nat → 𝒪[L]ˣ`, and `d : Nat`, this proves exactly `chosenNormalBasisPrincipalUnitCorrectionProduct_succStatement L z d`. No convergence, principal-unit membership, normal-basis or field-extension assumption is present.

The proof is `rfl`, as in the source: the successor branch of the published recursive `chosenNormalBasisPrincipalUnitCorrectionProduct` is the preceding product multiplied on the right by `z d`. The source `[simp]` attribute is restored on this theorem. The sole direct import is the published `NormalBasisInfiniteProduct.CorrectionProductStatements` module, which imports `CorrectionProduct`; its Mathlib dependency supplies the actual valuation-ring units. This proof concerns finite recursive products.

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
