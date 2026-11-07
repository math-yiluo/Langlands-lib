# `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The 2 `p2m_reactivate "…"` commands (an FLT `P2M.Util` command that re-activates the scoped extensions of the named namespaces) become `open scoped` of the same namespaces, written with `_root_.`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq`.

Auxiliary namespace `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort`
(sub-namespace `IsLocalRing`). The argument is the transitivity `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` of Serre, Local
Fields, IV §3, Proposition 15, deduced from the lower-numbering compatibility.

- `herbrandPhiCeil R H n := sInf {k : ℕ | herbrandPhi R H n ≤ k}` with `herbrandPhiCeil_eq_ceil` and the scoped
  simp lemma `herbrandPhiCeil_zero`; the Prop-valued definitions `LowerHerbrandQuotientCompat R G S H` (as in the
  module `S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`)
  and `HerbrandPhiTowerCompat R G S H` (`∀ u ≥ 0, φ_G(u) = φ_{G/H}(φ_H(u))`, with `φ_G = herbrandPhi R G`,
  `φ_H = herbrandPhi R H`, `φ_{G/H} = herbrandPhi S (G ⧸ H)`); `herbrandPhi_tower_zero` and
  `HerbrandPhiTowerCompat.natCast`.
- Divisibility of the orders: `lowerRamificationCard_dvd_of_le` (`|G_j| ∣ |G_i|` for `i ≤ j`),
  `lowerRamificationCard_dvd_zero`, `lowerRamificationCard_dvd_sum_Icc` (`|G_{m+1}| ∣ ∑ i ∈ Icc 1 m, |G_i|`),
  `herbrandPhi_natCast_eq_cast_div`, `one_le_herbrandPhiCeil_succ` and `herbrandPhiCeil_succ_cast_sub_one_le`
  (`⌈φ(m+1)⌉ - 1 ≤ φ(m)`).
- `card_lowerRamificationGroup_map_mul_card_subgroup`: `|image of G_n in G ⧸ H| · |H_n| = |G_n|` (Lagrange for
  `G_n → G ⧸ H`, whose kernel `H ⊓ G_n` is `H_n` by `lowerRamificationGroup_map_subtype'`); hence, under
  `LowerHerbrandQuotientCompat`, `lowerRamificationCard_quotient_mul`:
  `|(G/H)_{⌈φ_H(n)⌉}| · |H_n| = |G_n|`.
- `herbrandPhi_mem_segment_phiCeil_succ`: `φ_H(m)` and `φ_H(m+1)` lie in one interval `[j, j+1]`,
  `j = ⌈φ_H(m+1)⌉ - 1`; so on `[m, m+1]` the composite `φ_{G/H} ∘ φ_H` is linear with slope
  `|(G/H)_{j+1}| / |(G/H)_0| · |H_{m+1}| / |H_0| = |G_{m+1}| / |G_0|` (the order identity at `m + 1` and at `0`):
  `herbrandPhi_comp_segment`. Then `herbrandPhi_comp_natCast` (induction on `n`) and `herbrandPhiTowerCompat`
  (every `u ≥ 0` lies in the segment starting at `⌊u⌋₊`).
- The two `open scoped` commands (the ported `p2m_reactivate`) re-activate the scoped simp lemma after the
  namespace is closed.

`solution` turns `hH` into `LowerHerbrandQuotientCompat` (rewriting the ceiling as `herbrandPhiCeil`) and applies
`herbrandPhiTowerCompat` at `u`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhiCeil`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhiCeil_eq_ceil`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhiCeil_zero`
- def `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompat`
- def `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.HerbrandPhiTowerCompat`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhi_tower_zero`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.HerbrandPhiTowerCompat.natCast`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.lowerRamificationCard_dvd_of_le`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.lowerRamificationCard_dvd_zero`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.lowerRamificationCard_dvd_sum_Icc`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhi_natCast_eq_cast_div`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.one_le_herbrandPhiCeil_succ`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhiCeil_succ_cast_sub_one_le`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.card_lowerRamificationGroup_map_mul_card_subgroup`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompat.lowerRamificationCard_quotient_mul`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.herbrandPhi_mem_segment_phiCeil_succ`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompat.herbrandPhi_comp_segment`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompat.herbrandPhi_comp_natCast`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompat.herbrandPhiTowerCompat`
- theorem `P2MW.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup`.
Other imports: `Mathlib`.
