# Residue degree of an unramified valued extension: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrankStatement`
([target](ResidueDegreeStatement.md), NYLL source unit M161.003) by the theorem

```lean
theorem unramifiedValuation_residue_finrank_eq_finrank :
    unramifiedValuation_residue_finrank_eq_finrankStatement.{u}
```

in namespace `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`, the
adapted source name. Its type is the target at the same universe `u`. The theorem
says: for a finite extension `L/K` of nonarchimedean local fields with a valuation
extension, `𝒪[L]` finite over `𝒪[K]`, and an instance of the published class
`IsUnramifiedValuedExtension K L` (M161.001), the residue degree
`Module.finrank 𝓀[K] 𝓀[L]` equals `Module.finrank K L`.

## Proof

The proof is the source proof after an opening `intro`. It specializes the
formula `e · f = [L : K]` of M138.029 to `e = 1`. The two Library proofs it uses
each have a closed proposition `∀ (K L : Type u) [..], ..` as type; applied to
`K` and `L`, their instance arguments are found by instance search among the
introduced binders.

1. `intro K L` followed by anonymous introductions of the thirteen instance
   binders of the target.
2. `h` is `Langlands.NYLL.LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K L`
   (M138.029, [proof](../ResidueExtension/RamificationResidueDegreeProof.md)):
   `Ideal.ramificationIdx' 𝓂[K] 𝓂[L] * Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L`.
3. `hp : 𝓂[K] ≠ ⊥` is Mathlib's `Ring.ne_bot_of_isMaximal_of_not_isField`
   applied to the maximality of the maximal ideal of the local ring `𝒪[K]`
   (`IsLocalRing.maximalIdeal.isMaximal`) and to
   `IsDiscreteValuationRing.not_isField 𝒪[K]` (the integer ring of a
   nonarchimedean local field is a discrete valuation ring, so not a field).
4. Three rewrites in `h`:
   - Mathlib's `Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp` replaces
     `Ideal.ramificationIdx' 𝓂[K] 𝓂[L]` by `(𝓂[L]).ramificationIdx 𝒪[K]`. Its
     remaining hypotheses (`𝒪[K]` a domain, `𝒪[L]` a Dedekind domain
     torsion-free over `𝒪[K]`, `𝓂[L]` prime and lying over `𝓂[K]`) are found by
     instance search;
   - `unramifiedValuation_ramificationIdx_eq_one K L` (M161.002,
     [proof](RamificationIndexProof.md)) replaces it by `1`;
   - `one_mul`.
   Now `h` is the goal `Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L`, and
   `exact h` closes it.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module, together
with the four proof modules it depends on, with no errors or warnings. Inspection
of the theorem reported kind `theorem`, level parameters `[u]`, and only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.RamificationIndexProof`:
  the M161.002 proof `unramifiedValuation_ramificationIdx_eq_one`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueDegreeStatement`:
  the target and the class `IsUnramifiedValuedExtension`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationResidueDegreeProof`:
  the M138.029 proof `maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank`,
  and through its Mathlib imports the remaining lemmas used above.

The two proofs are separate focused contributions of the same task and are
imported by Lean name; this module does not copy them. The published target is
imported and used by name; it is not modified.

## Source correspondence and changes

The original theorem is
`LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrank`
at lines 57–74 (docstring at 57–58, theorem at 59, proof at 66–74) of Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean#L57-L74)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`b9c37585002a07b55997dd84ffdc7409fa5fee34fea04889196a4f617ddb909d`). Its
statement is the published target. The source proof uses the source theorems
`LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank`
(M138.029, `ResidueExtension.lean` line 384) and
`unramifiedValuation_ramificationIdx_eq_one` (M161.002, line 47), whose adapted
names are the two Library proofs above.

Worker 4699 made these changes on 15 November 2026:

1. Prefix the namespace with `Langlands.NYLL`; keep the theorem name.
2. State the theorem's type as the published closed proposition
   `unramifiedValuation_residue_finrank_eq_finrankStatement.{u}` instead of the
   source binders and conclusion, and introduce the binders with `intro`.
3. Keep the source proof lines unchanged, except that the explicit reference
   `LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank`
   becomes `Langlands.NYLL.LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank`,
   the adapted name.
4. The source docstring repeats the sentence "For an unramified valued extension,
   the residue-field degree equals the field-extension degree."; keep it once and
   add one sentence naming the target.
5. Replace the source imports by the published statement module and the two
   proof modules above, and omit the source's `noncomputable section`.
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
