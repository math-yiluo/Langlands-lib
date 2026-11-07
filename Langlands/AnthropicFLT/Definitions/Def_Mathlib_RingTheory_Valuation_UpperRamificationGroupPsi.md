# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Further properties of `herbrandPhi`, `herbrandPsi` and the upper numbering of
`Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup` (namespace `IsLocalRing`; `R` local with a
`MulSemiringAction` of `G`, `G_i` the lower groups). Every result below except `herbrandPhi_natCast_succ` and
`herbrandPhi_segment` assumes `Finite G`; the `ValuationSubring` wrappers assume that the decomposition subgroup
is finite. In particular `herbrandPsi` is shown to be an inverse of `herbrandPhi` only for finite `G`.

- Segment formulas: `herbrandPhi_natCast_succ` (`φ(m + 1) = φ(m) + |G_{m+1}| / |G_0|`), `herbrandPhi_segment`
  (`φ(u) = φ(m) + (u - m) |G_{m+1}| / |G_0|` for `m ≤ u ≤ m + 1`) and `herbrandPhi_segment_solve` (the explicit
  preimage of `v ∈ [φ(m), φ(m+1)]`).
- `herbrandPhi_surjective`, `herbrandPhi_bijective`; `herbrandPhi_herbrandPsi` (`φ (ψ v) = v`), so that
  `herbrandPsi` is a two-sided inverse (`herbrandPsi_rightInverse`, `herbrandPsi_leftInverse`), strictly monotone
  and bijective (`herbrandPsi_strictMono`, `_monotone`, `_injective`, `_surjective`, `_bijective`).
- The order equivalences `herbrandPsi_le_iff` (`ψ v ≤ u ↔ v ≤ φ u`), `le_herbrandPsi_iff`,
  `herbrandPsi_lt_iff`, `lt_herbrandPsi_iff`; `herbrandPsi_of_nonpos` (`ψ v = v` for `v ≤ 0`),
  `herbrandPsi_nonneg`, `herbrandPsi_pos` and `herbrandPsi_segment` (`ψ` on `[φ(m), φ(m+1)]`).
- The upper index: `upperRamificationIndex_eq_zero_iff` (`= 0 ↔ v ≤ 0`), `upperRamificationIndex_eq_succ_iff`
  (`= m + 1 ↔ φ(m) < v ≤ φ(m+1)`), `upperRamificationIndex_eq_iff`, `upperRamificationGroup_of_lt_of_le`
  (`G^v = G_{m+1}` for `φ(m) < v ≤ φ(m+1)`), `upperRamificationGroup_eq_of_segment`,
  `upperRamificationIndex_eq_ceil_herbrandPsi` (`upperRamificationIndex R G v = ⌈ψ v⌉₊`) and
  `upperRamificationGroup_eq_ceil_herbrandPsi` (`G^v = G_{⌈ψ v⌉₊}`).
- `ValuationSubring` wrappers: `herbrandPhi_surjective`, `herbrandPhi_herbrandPsi`, `herbrandPsi_strictMono`,
  `herbrandPsi_monotone`, `upperRamificationGroup_of_lt_of_le`.

Section `Gates` contains 4 `example` checks of the definitions. The file ends with 11 `#guard_msgs in #print axioms` checks (kept from FLT), for `IsLocalRing.herbrandPhi_natCast_succ`, `IsLocalRing.herbrandPhi_segment`, `IsLocalRing.herbrandPhi_segment_solve`, `IsLocalRing.herbrandPhi_surjective`, `IsLocalRing.herbrandPhi_herbrandPsi`, `IsLocalRing.herbrandPsi_strictMono`, `IsLocalRing.herbrandPsi_segment`, `IsLocalRing.upperRamificationIndex_eq_succ_iff`, `IsLocalRing.upperRamificationGroup_of_lt_of_le`, `IsLocalRing.upperRamificationGroup_eq_ceil_herbrandPsi`, `ValuationSubring.herbrandPhi_herbrandPsi`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `IsLocalRing.herbrandPhi_natCast_succ`
- theorem `IsLocalRing.herbrandPhi_segment`
- theorem `IsLocalRing.herbrandPhi_segment_solve`
- theorem `IsLocalRing.herbrandPhi_surjective`
- theorem `IsLocalRing.herbrandPhi_bijective`
- theorem `IsLocalRing.herbrandPhi_herbrandPsi`
- theorem `IsLocalRing.herbrandPsi_rightInverse`
- theorem `IsLocalRing.herbrandPsi_leftInverse`
- theorem `IsLocalRing.herbrandPsi_strictMono`
- theorem `IsLocalRing.herbrandPsi_monotone`
- theorem `IsLocalRing.herbrandPsi_injective`
- theorem `IsLocalRing.herbrandPsi_surjective`
- theorem `IsLocalRing.herbrandPsi_bijective`
- theorem `IsLocalRing.herbrandPsi_le_iff`
- theorem `IsLocalRing.le_herbrandPsi_iff`
- theorem `IsLocalRing.herbrandPsi_lt_iff`
- theorem `IsLocalRing.lt_herbrandPsi_iff`
- theorem `IsLocalRing.herbrandPsi_of_nonpos`
- theorem `IsLocalRing.herbrandPsi_nonneg`
- theorem `IsLocalRing.herbrandPsi_pos`
- theorem `IsLocalRing.herbrandPsi_segment`
- theorem `IsLocalRing.upperRamificationIndex_eq_zero_iff`
- theorem `IsLocalRing.upperRamificationIndex_eq_succ_iff`
- theorem `IsLocalRing.upperRamificationIndex_eq_iff`
- theorem `IsLocalRing.upperRamificationGroup_of_lt_of_le`
- theorem `IsLocalRing.upperRamificationGroup_eq_of_segment`
- theorem `IsLocalRing.upperRamificationIndex_eq_ceil_herbrandPsi`
- theorem `IsLocalRing.upperRamificationGroup_eq_ceil_herbrandPsi`
- theorem `ValuationSubring.herbrandPhi_surjective`
- theorem `ValuationSubring.herbrandPhi_herbrandPsi`
- theorem `ValuationSubring.herbrandPsi_strictMono`
- theorem `ValuationSubring.herbrandPsi_monotone`
- theorem `ValuationSubring.upperRamificationGroup_of_lt_of_le`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`.
Other imports: `Mathlib`.
