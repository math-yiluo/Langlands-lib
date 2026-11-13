# Successive principal-unit quotient targets (M132.006–007)

These are unproved Prop-valued definitions of the source theorem statements.
They preserve each source binder, its implicit or explicit kind, and its order.
Their values are the original conclusions. No theorem proof is submitted.

| Unit | Source declaration and lines | Adapted declaration |
| --- | --- | --- |
| M132.006 | `LocalFieldTheory.principalUnitsSuccQuotLift_mk`, 80–87 | `Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotLift_mkStatement` |
| M132.007 | protected `LocalFieldTheory.PrincipalUnitsSuccQuot.inductionOn`, 90–104 | protected `Langlands.NYLL.LocalFieldTheory.PrincipalUnitsSuccQuot.inductionOnStatement` |

The evaluation target keeps `{K : Type u} {M : Type*}`, `[Field K]`,
`[ValuativeRel K]`, `[Group M]`, then `n`, `f`, the explicit kernel containment
`h`, and the explicit representative `x`. It says that lifting and then
applying the quotient map evaluates to `f x`. The universe of `M` is independent.

The induction target keeps implicit `K`, both field and valuation instances,
explicit `n`, implicit `motive : PrincipalUnitsSuccQuot K n → Prop`, explicit
class `q`, and explicit representative-wise proof argument `h`, in source order.
Its value is precisely `motive q`; the premise `h` is retained as a parameter
and is not replaced by an implication or a different elimination principle.
The protected declaration status is preserved.

Modifications: prefix `Langlands.NYLL`, append `Statement` to theorem names,
replace theorem/lemma commands by `def ... : Prop :=` with the former conclusion
as body, and omit proof bodies. The `[simp]` theorem attribute is omitted because
these declarations define propositions and prove no rewrite rule.
Only `SuccessorDefinitions` is imported. All source universe, notation and
noncomputable section commands are retained. There are no new instances.
The actual source quotient, quotient map and lift come from that data module;
Mathlib's generic quotient induction and lift evaluation are the underlying
construction tools, but do not replace these exact named targets.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`.
The complete source file SHA-256 is
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata notes.

The original copyright, Apache-2.0 license and author header are retained.
The Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 211 performed this extraction and namespace adaptation. No patch10 edit
or other worker's implementation draft was used.
