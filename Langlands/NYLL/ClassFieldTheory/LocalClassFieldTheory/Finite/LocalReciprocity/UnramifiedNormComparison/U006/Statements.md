# The canonical projection formula: proposition target

This module adapts NYLL M267.006 as the closed proposition
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupEquivAbelianizationOfUnramifiedValuation_applyStatement`.
It asserts that, for every automorphism `σ : Gal(L / K)`, the named
`galoisGroupEquivAbelianizationOfUnramifiedValuation K L` sends `σ` to
`Abelianization.of σ`, the canonical projection to the abelianization.
It is a target, with no proof or simp attribute in this module.

## Parameters and imports

The entire original section telescope is retained in order. `K L : Type`
remain in universe zero. Both fields have `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances, followed by
`Algebra K L`, `FiniteDimensional K L`, `IsGalois K L`, the extension of the
valuations, the integral-closure instance
`IsIntegralClosure 𝒪[L] 𝒪[K] L`, `Module.Finite 𝒪[K] 𝒪[L]`, and the
published unramified class
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L`
(M161.001). The automorphism `σ` is the final explicit parameter.
No hypothesis supplies the equation, cyclicity, or an equivalence.

The sole import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U005.Definitions`,
which provides the specific named source adaptation and Mathlib's
`Abelianization.of`. The equality has codomain `Abelianization (Gal(L / K))`.
The imported definition constructs its equivalence using only local cyclic
and commutative-group instances.

## Source correspondence and modifications

The pinned original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean#L103-L109)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
M267.006 occupies lines 103–109: doc comment, simp attribute, and theorem
`LocalClassFieldTheory.galoisGroupEquivAbelianizationOfUnramifiedValuation_apply`.
The shared section parameters occupy lines 34–44.

Worker 205 made these changes on 14 November 2026: extract this target,
prefix the namespace with `Langlands.NYLL`, close the full original Type-0
telescope into a `Prop`-valued definition with suffix `Statement`, and
replace the source imports by the focused U005 module. The equation and
parameters are unchanged. The original `rfl` proof and simp attribute are
reserved for a separate proof unit. The original copyright, authorship and
doc comment are retained. No other worker's unpublished draft was used for
this target; the imported definition credits Worker 3's cyclicity argument.

## Checks

The focused `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) compiled this target with no
errors or warnings at Library base `c0debd6f4dd02fdd68d70811cf610906b945a962`
(record `2bd83817-d8eb-4fb8-bd70-8647afdd3067`). Exact inspection reported `statement_returns_prop: true`,
no universe parameters, and only `propext`, `Classical.choice` and `Quot.sound`.
The imported U005 definition is published in the Library. This target is submitted
for independent statement review; proof acceptance remains a separate unit.

## Provenance and license

The source registration is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Apache-2.0 license and notices are retained at
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
