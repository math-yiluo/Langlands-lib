# `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField`.

Auxiliary namespace `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.HerbrandPortE`,
with one lemma `module_finite_fixedPoints_subring` (the same statement and proof as in the module
`S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints`).

Proof of `solution`. The fixed subrings `R^G` and `R^H` are discrete valuation rings
(`FixedPoints.isDiscreteValuationRing_subring`), `R` is finite over `R^G`, and `R^G → R` is a local homomorphism
with separable residue field extension, so `R = R^G[x]` for some `x`
(`IsDiscreteValuationRing.exists_adjoin_singleton_eq_top_of_isSeparable_residueField`). With the inclusion
`R^G ⊆ R^H` as an algebra, `R^H` is finite over `R^G` (submodule of the finite module `R`), the map is local, and
its residue field extension is separable (a subextension of a separable one), so `R^H = R^G[y']` for some `y'`;
transporting along `R^H → R`, every element of `R^H` lies in `Algebra.adjoin R^G {y'}` inside `R`. Next `𝔪_R` lies
over `𝔪_{R^H}` (`FixedPoints.maximalIdeal_subring_eq_comap`) and the residue extension of `R` over `R^H` is
separable (top of a separable tower), so the scaling
`IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints` holds for `H`. Finally
`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top` with `A = R^G` (every `σ`
fixes `R^G`), `x`, `y'` and the scaling gives the claim.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.HerbrandPortE.module_finite_fixedPoints_subring`
- theorem `P2MW.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup`, `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`, `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints`, `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField`, `Langlands.AnthropicFLT.Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring`.
Other imports: `Mathlib`.
