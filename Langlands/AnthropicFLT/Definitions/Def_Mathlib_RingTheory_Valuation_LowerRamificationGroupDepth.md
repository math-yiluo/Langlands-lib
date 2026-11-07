# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The ramification depth `i_G(σ)` and finiteness of the lower filtration.

- `Subgroup.exists_eq_bot_of_antitone_of_iInf_eq_bot`: in a finite group an antitone sequence of subgroups with
  trivial intersection is eventually `⊥`.
- For a local ring `R` with a `MulSemiringAction` of `G`: `smul_mem_maximalIdeal_pow_iff`,
  `exists_lowerRamificationGroup_eq_bot` (for finite `G` acting faithfully with `⨅ n, 𝔪ⁿ = ⊥`, `G_i = ⊥` for all
  large `i`), `lowerRamificationGroup_finiteIndex` (finite `G`) and `isOpen_lowerRamificationGroup` (discrete
  topology on `G`).
- For a discrete valuation ring `R` (namespace `IsDiscreteValuationRing`, valuation `addVal R : R → ℕ∞`):
  `mem_maximalIdeal_pow_iff_le_addVal` (`x ∈ 𝔪ⁿ ↔ n ≤ addVal R x`), `iInf_maximalIdeal_pow_eq_bot`, `addVal_smul`
  (`addVal R (σ • x) = addVal R x`), and the definition
  `ramificationDepth R G σ := ⨅ x : R, addVal R (σ • x - x)` (value in `ℕ∞`; Serre's `i_G(σ)` of Local Fields
  IV §1, with `i_G(1) = ∞`). Lemmas: `ramificationDepth_def`, `le_ramificationDepth_iff`,
  `mem_lowerRamificationGroup_iff_le_ramificationDepth` (`σ ∈ G_i ↔ i + 1 ≤ i_G(σ)`),
  `setOf_add_one_le_ramificationDepth_eq`, `ramificationDepth_one` (`= ⊤`), `ramificationDepth_eq_top_iff`
  (for a faithful action, `i_G(σ) = ⊤ ↔ σ = 1`), `exists_lowerRamificationGroup_eq_bot` (finite faithful `G`) and
  `isOpen_setOf_le_ramificationDepth`.
- `ValuationSubring.ramificationDepth` for a discrete valuation subring and its decomposition subgroup, with
  `mem_lowerRamificationGroup_iff_le_ramificationDepth` and `exists_lowerRamificationGroup_eq_bot`.

Section `Gates` contains 4 `example` checks of the definitions. The file ends with 13 `#guard_msgs in #print axioms` checks (kept from FLT), for `IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal`, `IsDiscreteValuationRing.iInf_maximalIdeal_pow_eq_bot`, `IsDiscreteValuationRing.addVal_smul`, `IsDiscreteValuationRing.ramificationDepth`, `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_ramificationDepth`, `IsDiscreteValuationRing.ramificationDepth_eq_top_iff`, `Subgroup.exists_eq_bot_of_antitone_of_iInf_eq_bot`, `IsLocalRing.exists_lowerRamificationGroup_eq_bot`, `IsDiscreteValuationRing.exists_lowerRamificationGroup_eq_bot`, `IsLocalRing.lowerRamificationGroup_finiteIndex`, `IsLocalRing.isOpen_lowerRamificationGroup`, `ValuationSubring.mem_lowerRamificationGroup_iff_le_ramificationDepth`, `ValuationSubring.exists_lowerRamificationGroup_eq_bot`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Subgroup.exists_eq_bot_of_antitone_of_iInf_eq_bot`
- theorem `IsLocalRing.smul_mem_maximalIdeal_pow_iff`
- theorem `IsLocalRing.exists_lowerRamificationGroup_eq_bot`
- theorem `IsLocalRing.lowerRamificationGroup_finiteIndex`
- theorem `IsLocalRing.isOpen_lowerRamificationGroup`
- theorem `IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal`
- theorem `IsDiscreteValuationRing.iInf_maximalIdeal_pow_eq_bot`
- theorem `IsDiscreteValuationRing.addVal_smul`
- def `IsDiscreteValuationRing.ramificationDepth`
- theorem `IsDiscreteValuationRing.ramificationDepth_def`
- theorem `IsDiscreteValuationRing.le_ramificationDepth_iff`
- theorem `IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_le_ramificationDepth`
- theorem `IsDiscreteValuationRing.setOf_add_one_le_ramificationDepth_eq`
- theorem `IsDiscreteValuationRing.ramificationDepth_one`
- theorem `IsDiscreteValuationRing.ramificationDepth_eq_top_iff`
- theorem `IsDiscreteValuationRing.exists_lowerRamificationGroup_eq_bot`
- theorem `IsDiscreteValuationRing.isOpen_setOf_le_ramificationDepth`
- def `ValuationSubring.ramificationDepth`
- theorem `ValuationSubring.mem_lowerRamificationGroup_iff_le_ramificationDepth`
- theorem `ValuationSubring.exists_lowerRamificationGroup_eq_bot`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup`.
Other imports: `Mathlib`.
