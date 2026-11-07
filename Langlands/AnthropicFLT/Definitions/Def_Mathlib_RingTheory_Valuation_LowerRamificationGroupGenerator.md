# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Computing ramification depths with a generator.

- `Polynomial.sub_dvd_aeval_sub` (`x - y ∣ p(x) - p(y)`), `AlgHom.sub_dvd_sub_of_mem_adjoin_singleton` (for an
  `A`-algebra endomorphism `σ` of `R` and `r ∈ Algebra.adjoin A {x}`, `σ x - x ∣ σ r - r`) and
  `AlgHom.sub_dvd_sub_of_adjoin_singleton_eq_top`; the same for an element `σ` of a monoid acting on `R` that fixes
  the image of `A` (`MulSemiringAction.smul_sub_dvd_smul_sub_of_mem_adjoin_singleton`,
  `…_of_adjoin_singleton_eq_top`).
- For a discrete valuation ring `R` with a `MulSemiringAction` of `G`, an `A`-algebra structure on `R`, an element
  `σ` fixing the image of `A` (hypothesis `hfix`) and a generator `x` with `Algebra.adjoin A {x} = ⊤`:
  `addVal_smul_sub_le_of_adjoin_singleton_eq_top` (`addVal (σ • x - x) ≤ addVal (σ • r - r)` for every `r`),
  `ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top` (`i_G(σ) = addVal R (σ • x - x)`, Serre, Local Fields
  IV §1 Lemma 1), the criteria `mem_lowerRamificationGroup_iff_le_addVal_of_adjoin_singleton_eq_top`
  (`σ ∈ G_i ↔ i + 1 ≤ addVal R (σ • x - x)`) and `mem_lowerRamificationGroup_iff_smul_sub_mem_pow_of_adjoin_singleton_eq_top`
  (`↔ σ • x - x ∈ 𝔪^(i+1)`), `addVal_smul_sub_eq_of_adjoin_singleton_eq_top` (independence of the generator), and
  the variants `ramificationDepth_eq_addVal_of_smulCommClass`, `mem_lowerRamificationGroup_iff_le_addVal_of_smulCommClass`
  under `SMulCommClass G A R`.
- `ValuationSubring` versions: `ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top`,
  `mem_lowerRamificationGroup_iff_le_addVal_of_adjoin_singleton_eq_top`.

Section `Gates` contains 5 `example` checks of the definitions. The file ends with 14 `#guard_msgs in #print axioms` checks (kept from FLT), for `Polynomial.sub_dvd_aeval_sub`, `AlgHom.sub_dvd_sub_of_mem_adjoin_singleton`, `AlgHom.sub_dvd_sub_of_adjoin_singleton_eq_top`, `MulSemiringAction.smul_sub_dvd_smul_sub_of_mem_adjoin_singleton`, `MulSemiringAction.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top`, `IsDiscreteValuationRing.addVal_smul_sub_le_of_adjoin_singleton_eq_top`, `IsDiscreteValuationRing.ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top`, `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_addVal_of_adjoin_singleton_eq_top`, `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_smul_sub_mem_pow_of_adjoin_singleton_eq_top`, `IsDiscreteValuationRing.addVal_smul_sub_eq_of_adjoin_singleton_eq_top`, `IsDiscreteValuationRing.ramificationDepth_eq_addVal_of_smulCommClass`, `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_addVal_of_smulCommClass`, `ValuationSubring.ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top`, `ValuationSubring.mem_lowerRamificationGroup_iff_le_addVal_of_adjoin_singleton_eq_top`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Polynomial.sub_dvd_aeval_sub`
- theorem `AlgHom.sub_dvd_sub_of_mem_adjoin_singleton`
- theorem `AlgHom.sub_dvd_sub_of_adjoin_singleton_eq_top`
- theorem `MulSemiringAction.smul_sub_dvd_smul_sub_of_mem_adjoin_singleton`
- theorem `MulSemiringAction.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top`
- theorem `IsDiscreteValuationRing.addVal_smul_sub_le_of_adjoin_singleton_eq_top`
- theorem `IsDiscreteValuationRing.ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top`
- theorem `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_addVal_of_adjoin_singleton_eq_top`
- theorem `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_smul_sub_mem_pow_of_adjoin_singleton_eq_top`
- theorem `IsDiscreteValuationRing.addVal_smul_sub_eq_of_adjoin_singleton_eq_top`
- theorem `IsDiscreteValuationRing.ramificationDepth_eq_addVal_of_smulCommClass`
- theorem `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_addVal_of_smulCommClass`
- theorem `ValuationSubring.ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top`
- theorem `ValuationSubring.mem_lowerRamificationGroup_iff_le_addVal_of_adjoin_singleton_eq_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`.
Other imports: `Mathlib`.
