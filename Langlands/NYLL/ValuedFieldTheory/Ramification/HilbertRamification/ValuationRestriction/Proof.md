# Valuation-ring action and normal restriction: exact proof

Worker 579, 14 November 2026. This module proves
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_integerMap_restrictNormalStatement`
by the theorem
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_integerMap_restrictNormal`,
in module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationRestriction.Proof`.
It imports the published target from the sibling `Statements` module without
changing that module or its dependencies.

## Exact scope

The theorem preserves the complete target telescope: fields `K : Type u`,
`L : Type w`, `M : Type y`; the three supplied algebras; `IsScalarTower K L M`;
`Normal K L`; the chosen discrete valuation fields
`base : DVF.{u,v} K`, `middle : DVF.{w,x} L`, `target : DVF.{y,z} M`; and all
three valuation-extension instances. All six universe levels are independent.
The explicit arguments are the unique-extension witnesses `hmiddle` and
`htarget`, the actual automorphism `σ : Gal(M/K)`, and
`a : middle.valuationSubring`. The witness universe specializations remain
`HasUniqueValuationExtension.{u,v,w,x,x}` and
`HasUniqueValuationExtension.{u,v,y,z,z}`. No finiteness or additional
normality assumption is used.

The conclusion is the fully applied published proposition. It equates two
elements of the chosen target valuation ring: acting by `σ` on the canonical
image of `a`, and including the result of acting by `σ.restrictNormal L` on
`a`. The canonical map is
`algebraMap middle.valuationSubring target.valuationSubring`.

## Implemented proof

Apply `Subtype.ext` to reduce equality in the valuation ring to equality in
`M`. The definition of the published valuation-ring automorphism and the
canonical valuation-ring algebra map reduce this goal to

```lean
σ (algebraMap L M (a : L)) =
  algebraMap L M ((σ.restrictNormal L) (a : L))
```

The symmetric form of `AlgEquiv.restrictNormal_commutes σ L (a : L)` proves
this equality. This Mathlib theorem is in
`Mathlib/FieldTheory/Normal/Defs.lean`, lines 175–178 in the approved pin.
The unique-extension hypotheses ensure that the already published actions
land in the chosen valuation rings; the remaining equality is the normal
restriction identity on the field elements.

## Source, attribution and adaptations

This is the proof of M398.001, Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationRestriction.lean`,
lines 23–65](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationRestriction.lean#L23-L65).
The retained source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationRestriction.lean`,
SHA-256 `1eefe68fac7f1bd51c7f232dee148b4fcd1a134d9e5ee2104bb94dd116664904`.
Its complete lines 1–70 were read, including the proof at lines 61–65.
The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The accompanying registered supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata were found in the current published errata notes.

The proof body follows the source argument unchanged. Worker 579 isolated
the theorem, prefixed the namespace with `Langlands.NYLL`, imported the
published target, and replaced its displayed equality conclusion by that
fully applied Prop-valued target. The target already uses the canonical
`algebraMap` in place of the source's definitionally identical `integerMap`;
the sibling [statement documentation](Statements.md) records that adaptation.
The complete six-universe context and explicit witness universe
specializations are retained. The source's unused `noncomputable section`
and `ValuedExtension` open are omitted. No new definitions or instances are
introduced.

The original copyright, author, and Apache-2.0 notices are retained in the
Lean header. The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Validation

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The terminal development check
`f49e4a36-d284-43e1-b335-11782dd05244` compiled the proof module with zero
errors and zero warnings. The terminal Lake build and declaration inspection
`b2ede724-134b-4874-9ce2-567ba035bffd` also succeeded with zero errors and
zero warnings. It identified the theorem in this module, retained the exact
universe-parameter list `[u, v, w, x, y, z]`, and reported only the standard
assumptions `propext`, `Classical.choice`, and `Quot.sound`.
These development checks do not establish acceptance. Independent review,
exact-target validation, and Library publication are separate requirements.
