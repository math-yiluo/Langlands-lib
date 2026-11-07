# `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth`.

Auxiliary namespace `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort`.
The argument follows Serre, Local Fields, IV §3 (Lemma 5 and Herbrand's theorem), at integer indices.

- `FixedPoints.coe_quotientMk_smul_sub_subring` (as in the coset-identity module).
- `IsLocalRing.herbrandPhiCeil R H n := sInf {k : ℕ | herbrandPhi R H n ≤ k}` with `herbrandPhiCeil_eq_ceil`
  (`= ⌈herbrandPhi R H n⌉₊`), and the Prop-valued definitions `LowerHerbrandQuotientCompat R G S H`
  (`∀ n, (G_n).map (QuotientGroup.mk' H) = (G ⧸ H)_{herbrandPhiCeil R H n}` for an action of `G ⧸ H` on a local ring
  `S`) and `LowerHerbrandQuotientCompatCanonical R G H` (the case `S = FixedPoints.subring R H`).
- The private `sum_range_succ_eq_sum_Icc_one_add`, and properties of `i_G = ramificationDepth R G`:
  `addVal_sub_swap`, `ramificationDepth_le_addVal_smul_sub`, `le_ramificationDepth`, `addVal_inv_smul_sub`,
  `ramificationDepth_mul` (`min (i_G σ) (i_G τ) ≤ i_G (σ τ)`), `ramificationDepth_inv`,
  `ramificationDepth_eq_of_forall_smul_eq`, `mem_lowerRamificationGroup_iff_lt_ramificationDepth`,
  `lowerRamificationCard_eq_card_lt_ramificationDepth`, `sum_lowerRamificationCard_eq_sum_toNat_min_ramificationDepth`,
  `lowerRamificationCard_zero_mul_herbrandPhi_natCast_add_one`
  (`|G_0| (φ(n) + 1) = ∑ σ, min(i_G(σ), n + 1)`), `ramificationDepth_mul_eq_right_of_lt`.
- The same `fixedSubringRamificationDepth`, `cosetRamificationDepthSum` and `RamificationDepthCosetLemma` as in the
  coset-identity module (re-declared in this namespace), with `fixedSubringRamificationDepth_one`,
  `ramificationDepth_le_fixedSubringRamificationDepth`, `ramificationDepth_subgroup_coe`,
  `cosetRamificationDepthSum_eq_top_of_mem` and `cosetRamificationDepthSum_ne_top`.
- Coset maxima: `exists_max_ramificationDepth_coset`, `exists_quotientMk_eq_max_ramificationDepth` (each coset has
  a representative `τ₀` maximising `i_G` on it) and `ramificationDepth_mul_coe_eq_min`
  (`i_G(τ₀ h) = min(i_H(h), i_G(τ₀))` then); hence `sum_toNat_ramificationDepth_coset_eq` and
  `cosetRamificationDepthSum_toNat_eq` (if `i_G(τ₀) = n + 1`, the coset sum is `|H_0| (φ_H(n) + 1)`) and
  `cosetRamificationDepthSum_eq_zero_of_eq_zero`.
- From the coset identity `hc` and the scaling `addVal R y = e · addVal (fixed subring) y`:
  `RamificationDepthCosetLemma.fixedSubringRamificationDepth_ne_top`, `toNat_fixedSubringRamificationDepth_eq`,
  `fixedSubringRamificationDepth_eq_mul_ramificationDepth`, `mul_ramificationDepth_eq_cosetSum`, and
  `toNat_ramificationDepth_quotient_eq`: with `e = |H_0|`, `i_{G/H}(τ₀ H) = φ_H(n) + 1` when `i_G(τ₀) = n + 1`
  and `τ₀` is maximal in its coset (Serre's `i_{G/H}(σ) - 1 = φ(i_G(τ) - 1)`).
- `mem_lowerRamificationGroup_map_iff_max_depth` (for a maximal representative, `τ₀ H` lies in the image of `G_n`
  iff `n + 1 ≤ i_G(τ₀)`), `ramificationDepth_quotient_ne_top`, `ramificationDepth_quotient_eq_zero`, and
  `depth_iff_depth`: `n + 1 ≤ i_G(τ₀) ↔ herbrandPhiCeil R H n + 1 ≤ i_{G/H}(τ₀ H)` (using strict monotonicity of
  `φ_H`).
- `lowerHerbrandQuotientCompatCanonical_of_cosetLemma`: compare membership elementwise, choosing a maximal
  representative of each nontrivial class.

`solution` applies the last lemma to `hH` and `he` and rewrites `herbrandPhiCeil` as the ceiling.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.FixedPoints.coe_quotientMk_smul_sub_subring`
- def `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsLocalRing.herbrandPhiCeil`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsLocalRing.herbrandPhiCeil_eq_ceil`
- def `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompat`
- def `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsLocalRing.LowerHerbrandQuotientCompatCanonical`
- private theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.sum_range_succ_eq_sum_Icc_one_add`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.addVal_sub_swap`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_le_addVal_smul_sub`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.le_ramificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.addVal_inv_smul_sub`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_mul`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_inv`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_eq_of_forall_smul_eq`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.mem_lowerRamificationGroup_iff_lt_ramificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.lowerRamificationCard_eq_card_lt_ramificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.sum_lowerRamificationCard_eq_sum_toNat_min_ramificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.lowerRamificationCard_zero_mul_herbrandPhi_natCast_add_one`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_mul_eq_right_of_lt`
- def `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.fixedSubringRamificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.fixedSubringRamificationDepth_def`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.fixedSubringRamificationDepth_one`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_le_fixedSubringRamificationDepth`
- def `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum_def`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_subgroup_coe`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum_eq_top_of_mem`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum_ne_top`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.ramificationDepth_mul_coe_eq_min`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.exists_max_ramificationDepth_coset`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.exists_quotientMk_eq_max_ramificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.sum_toNat_ramificationDepth_coset_eq`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum_toNat_eq`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum_eq_zero_of_eq_zero`
- def `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma.fixedSubringRamificationDepth_ne_top`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma.toNat_fixedSubringRamificationDepth_eq`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.fixedSubringRamificationDepth_eq_mul_ramificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma.mul_ramificationDepth_eq_cosetSum`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma.toNat_ramificationDepth_quotient_eq`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.mem_lowerRamificationGroup_map_iff_max_depth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma.ramificationDepth_quotient_ne_top`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma.ramificationDepth_quotient_eq_zero`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma.depth_iff_depth`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.HerbrandPort.IsDiscreteValuationRing.lowerHerbrandQuotientCompatCanonical_of_cosetLemma`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`.
Other imports: `Mathlib`.
