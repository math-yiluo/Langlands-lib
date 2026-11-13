# A valuation overring centred at the maximal ideal is equal (NYLL M110.017)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has implicit `L : Type v` with `[Field L]` (the only section
variables the statement uses; its single universe parameter is `v`), explicit
`R S : ValuationSubring L`, `hRS : R ≤ S` and
`hcenter : ValuationSubring.idealOfLE R S hRS = IsLocalRing.maximalIdeal R`.
Its type is
`valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement R S hRS hcenter`,
which unfolds to `S = R`.

Mathematically: for valuation rings `R ⊆ S` of `L`, Mathlib's
`ValuationSubring.idealOfLE R S hRS` is the prime of `R` obtained by pulling back
the maximal ideal of `S`, and `S` is the localization of `R` at that prime
(`ValuationSubring.ofPrime_idealOfLE`). If that prime is the maximal ideal of
`R`, the localization is `R` itself, so `S = R`.

## Implemented proof

After `unfold valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement`
the rest is the unchanged source tactic proof:

1. `hcenter_self`: `idealOfLE R R le_rfl = maximalIdeal R`, by unfolding
   `idealOfLE` to a comap along the identity inclusion (`change`) and `ext`/`rfl`.
2. `hle`: `idealOfLE R R le_rfl ≤ idealOfLE R S hRS`, since both sides equal
   `maximalIdeal R` by `hcenter_self` and `hcenter`.
3. `hOfPrime`: by the antitonicity `ValuationSubring.ofPrime_le_of_le`,
   `ofPrime R (idealOfLE R S hRS) ≤ ofPrime R (idealOfLE R R le_rfl)`.
4. `hSR`: rewriting both sides with `ValuationSubring.ofPrime_idealOfLE` turns
   `hOfPrime` into `S ≤ R`.
5. `le_antisymm hSR hRS` gives `S = R`.

Dependencies are Mathlib only (`Mathlib/RingTheory/Valuation/ValuationSubring.lean`:
`idealOfLE`, `ofPrime`, `ofPrime_le_of_le`, `ofPrime_idealOfLE`, `inclusion`);
no auxiliary declaration, instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean:376–408`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean#L376-L408)
(partition unit lines 376–413; docstring at lines 372–375).

| Original (namespace `ValuationTheory.DiscreteValuationField.Valuation`) | Adapted |
| --- | --- |
| Theorem `valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal`, lines 376–408 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion `S = R` (line 380) | `valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement R S hRS hcenter` |
| Tactic proof, lines 381–408 | Identical, preceded by one `unfold` |

Other adaptations: the `Langlands.NYLL` namespace prefix; the single statement
import in place of the source imports; the section variables are reduced to
`{L : Type v} [Field L]` and `universe v` (the source theorem uses no other
section variable, so its elaborated binders are unchanged); the
`noncomputable section` and the unused `ResidueField` open are omitted; the
docstring keeps the source's first sentence.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 133's dated modification record. Worker 133 extracted
this proof directly from the pinned original and the frozen statement module;
there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`, recomputed by
Worker 133 on 13 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m110)
lists this unit in module M110 (no patch10 edit applies).

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
