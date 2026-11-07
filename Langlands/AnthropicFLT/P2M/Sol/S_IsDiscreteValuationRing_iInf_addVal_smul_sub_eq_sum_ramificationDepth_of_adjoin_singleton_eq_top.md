# `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top`.

Auxiliary namespace `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort`.
The argument is the proof of Serre, Local Fields, IV §1, Proposition 3.

- `FixedPoints.coe_quotientMk_smul_subring`, `FixedPoints.coe_quotientMk_smul_sub_subring`: the action of the
  class of `g` in `G ⧸ H` on the fixed subring is the action of `g` (both `rfl`).
- Definitions: `fixedSubringRamificationDepth R G H σ := ⨅ x : FixedPoints.subring R H, addVal R (σ • x - x)` for
  `σ : G ⧸ H`, `cosetRamificationDepthSum R G H τ₀ := ∑ h : H, ramificationDepth R G (τ₀ * h)`, and the Prop
  `RamificationDepthCosetLemma R G H` (the two agree at `QuotientGroup.mk τ₀` for every `τ₀`).
- The polynomial `prodXSubSMulSubgroup R H x := ∏ h : H, (X - C (h • x))`: it vanishes at `x`, is fixed by `H`, has
  coefficients in the fixed subring, `g` acts on it by `∏ h, (X - C ((g h) • x))`, and over a domain it divides
  every polynomial vanishing at all `h • x` when these are distinct (`prodXSubSMulSubgroup_dvd_of_isRoot`).
- `smul_map_algebraMap`, `smul_aeval` (elements fixing `A` commute with evaluating polynomials over `A`), and
  `injective_subgroup_smul_of_adjoin_singleton_eq_top` (for a faithful action, `h ↦ h • x` is injective when
  `Algebra.adjoin A {x} = ⊤`).
- `smul_sub_dvd_prod_sub_smul`: `τ₀ • y₀ - y₀ ∣ ∏ h, (x - (τ₀ h) • x)` when every fixed element lies in
  `Algebra.adjoin A {y₀}` (apply `τ₀` to the coefficients of `prodXSubSMulSubgroup` and evaluate at `x`), and
  `prod_sub_smul_dvd_smul_sub`: the product divides `τ₀ • y₀ - y₀` when `y₀` is fixed (write `y₀ = f(x)` with `f`
  over `A`; `f - y₀` vanishes at every `h • x`, so `prodXSubSMulSubgroup` divides it; apply `τ₀` and evaluate at `x`).
- `addVal_finset_prod`, `fixedSubringRamificationDepth_eq_addVal` (the infimum is attained at the generator `y₀`),
  `cosetRamificationDepthSum_eq_addVal` (the sum is `addVal R (∏ h, (x - (τ₀ h) • x))`, by
  `ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top`), and `ramificationDepthCosetLemma_of_monogenic`
  (antisymmetry from the two divisibilities).

`solution` is `ramificationDepthCosetLemma_of_monogenic` at `τ`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.FixedPoints.coe_quotientMk_smul_subring`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.FixedPoints.coe_quotientMk_smul_sub_subring`
- def `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.fixedSubringRamificationDepth`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.fixedSubringRamificationDepth_def`
- def `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum_def`
- def `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.RamificationDepthCosetLemma`
- def `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.prodXSubSMulSubgroup`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.prodXSubSMulSubgroup_def`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.eval_prodXSubSMulSubgroup_self`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.smul_prodXSubSMulSubgroup`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.smul_coe_prodXSubSMulSubgroup`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.coeff_prodXSubSMulSubgroup_mem`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.eval_smul_prodXSubSMulSubgroup`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.prodXSubSMulSubgroup_dvd_of_isRoot`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.smul_map_algebraMap`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.smul_aeval`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.injective_subgroup_smul_of_adjoin_singleton_eq_top`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.smul_sub_dvd_prod_sub_smul`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.MulSemiringAction.prod_sub_smul_dvd_smul_sub`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.addVal_finset_prod`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.fixedSubringRamificationDepth_eq_addVal`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.cosetRamificationDepthSum_eq_addVal`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.HerbrandPort.IsDiscreteValuationRing.ramificationDepthCosetLemma_of_monogenic`
- theorem `P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`.
Other imports: `Mathlib`.
