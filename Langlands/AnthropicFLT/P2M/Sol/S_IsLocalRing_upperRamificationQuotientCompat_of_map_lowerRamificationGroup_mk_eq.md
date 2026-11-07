# `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq`.

Auxiliary namespace `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort`
(sub-namespace `IsLocalRing`).

- `lowerRamificationCard_dvd_of_le`, `lowerRamificationCard_dvd_zero`, `lowerRamificationCard_dvd_sum_Icc`,
  `herbrandPhi_natCast_eq_cast_div` (as in the φ-tower module, re-declared here),
  `sum_Icc_le_mul_of_herbrandPhi_natCast_le`, `exists_nat_segment_increment` and `exists_nat_herbrandPsi_natCast`:
  for finite `G`, `herbrandPsi R G` maps natural numbers to natural numbers (on the segment `[φ(m), φ(m+1)]`
  containing `n`, `ψ(n) = m + (n - φ(m)) |G_0| / |G_{m+1}|`, and `|G_{m+1}|` divides `n |G_0| - ∑ i ∈ Icc 1 m, |G_i|`).
- `ceil_herbrandPhi_upperRamificationIndex`: if `φ_G(n) = φ_{G/H}(φ_H(n))` for all natural `n`, then
  `⌈φ_H(upperRamificationIndex R G v)⌉₊ = upperRamificationIndex S (G ⧸ H) v` for every `v`. For `≤`, take the
  natural `m = ψ_H(k)` with `k` the upper index of `G ⧸ H`; then `v ≤ φ_G(m)`, so the upper index of `G` is at most
  `m`. For `≥`, `v ≤ φ_G(n) = φ_{G/H}(φ_H(n)) ≤ φ_{G/H}(⌈φ_H(n)⌉₊)`.

Proof of `solution`: the φ-tower at natural numbers comes from
`IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq hH`. For `v ≥ 0`, both
upper groups unfold to lower groups at the upper indices; rewriting the quotient's index with
`ceil_herbrandPhi_upperRamificationIndex` turns the goal into `hH` at the upper index of `G`. The hypothesis
`v ≥ 0` is not used by the argument. The file keeps FLT's `attribute [-simp]` line for four subgroup lemmas.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.lowerRamificationCard_dvd_of_le`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.lowerRamificationCard_dvd_zero`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.lowerRamificationCard_dvd_sum_Icc`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhi_natCast_eq_cast_div`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.sum_Icc_le_mul_of_herbrandPhi_natCast_le`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.exists_nat_segment_increment`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.exists_nat_herbrandPsi_natCast`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.ceil_herbrandPhi_upperRamificationIndex`
- theorem `P2MW.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi`, `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq`.
Other imports: `Mathlib`.
