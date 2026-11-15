# Ramification index of an unramified valued extension: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_oneStatement`
([target](RamificationIndexStatement.md), NYLL source unit M161.002) by the theorem

```lean
theorem unramifiedValuation_ramificationIdx_eq_one :
    unramifiedValuation_ramificationIdx_eq_oneStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`, the
adapted source name. Its type is the target at the same universe `u`. The theorem
says: for a finite extension `L/K` of nonarchimedean local fields with a valuation
extension, `𝒪[L]` finite over `𝒪[K]`, and an instance of the published class
`IsUnramifiedValuedExtension K L` (M161.001, in
[`Definitions`](Definitions.md)), the maximal ideal `𝓂[L]` has ramification
index `(𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1`.

## Proof

The proof is the source proof after an opening `intro`.

1. `intro K L` followed by anonymous introductions of the thirteen instance
   binders of the target, the last being `IsUnramifiedValuedExtension K L`.
2. `exact IsUnramifiedValuedExtension.maximalIdeal_ramificationIdx_eq_one
   (K := K) (L := L)`. The class's sole field
   `maximalIdeal_ramificationIdx_eq_one` is exactly the goal; its instance
   argument is the introduced class binder, found by instance search. The class
   has universe parameters `u v`; here both are `u`, as in the target.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module with no
errors or warnings. Inspection of the theorem reported kind `theorem`, level
parameters `[u]`, and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.RamificationIndexStatement`:
  the target, and through its import of `FiniteUnramified.Definitions` the class
  `IsUnramifiedValuedExtension`.

The published target and class are imported and used by name; neither is
modified.

## Source correspondence and changes

The original theorem is
`LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one`
at lines 46–55 (docstring at 46, theorem at 47, term proof at 54–55) of Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean#L46-L55)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`b9c37585002a07b55997dd84ffdc7409fa5fee34fea04889196a4f617ddb909d`). Its
statement is the published target.

Worker 4699 made these changes on 15 November 2026:

1. Prefix the namespace with `Langlands.NYLL`; keep the theorem name.
2. State the theorem's type as the published closed proposition
   `unramifiedValuation_ramificationIdx_eq_oneStatement.{u}` instead of the
   source binders and conclusion, and introduce the binders with `intro`.
3. Turn the source term proof (the class field projection, lines 54–55) into
   the `exact` step above, with the same term.
4. Keep the source docstring and add one sentence naming the target.
5. Replace the source imports by the published statement module, and omit the
   source's `noncomputable section`.
6. Keep the original copyright and author header verbatim and add the
   modification record.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged in the Library.
