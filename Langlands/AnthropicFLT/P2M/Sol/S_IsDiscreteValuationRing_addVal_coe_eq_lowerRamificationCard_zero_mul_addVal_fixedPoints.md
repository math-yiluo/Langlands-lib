# `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints`.

Auxiliary namespace `P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.HerbrandPortG3`.

- `module_finite_fixedPoints_subring`: for an integrally closed domain `R` with a faithful action of a finite group
  `H` whose fixed subring is noetherian and integrally closed, `R` is a finite module over the fixed subring (the
  fraction-field extension is Galois with group `H`, and `R` is the integral closure of the fixed subring in it).
- `addVal_algebraMap_irreducible_eq_ramificationIdx`: for an injective algebra map of discrete valuation rings
  `R → S` and a uniformizer `π` of `R`, `addVal S (π) = (maximalIdeal R).ramificationIdx' (maximalIdeal S)`.
- `addVal_map_eq_mul_of_irreducible`: if a ring hom `f : S → R` of discrete valuation rings sends a uniformizer
  to an element of valuation `e ≠ 0`, then `addVal R (f y) = e * addVal S y` for all `y`.

Proof of `solution`: `R` is finite over the fixed subring and `H` is a Galois group of the extension
(`FixedPoints.isGaloisGroup_subring`); the maximal ideal of the fixed subring is nonzero (a discrete valuation
ring is not a field). For a uniformizer `π` of the fixed subring, `addVal R π` is the ramification index, which
equals `ramificationIdxIn` and hence `Nat.card H_0 = lowerRamificationCard R H 0` by
`card_lowerRamificationGroup_zero_eq_ramificationIdxIn`; this is nonzero, and the last auxiliary lemma gives the
claim.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.HerbrandPortG3.module_finite_fixedPoints_subring`
- theorem `P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.HerbrandPortG3.addVal_algebraMap_irreducible_eq_ramificationIdx`
- theorem `P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.HerbrandPortG3.addVal_map_eq_mul_of_irreducible`
- theorem `P2MW.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`, `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup`, `Langlands.AnthropicFLT.Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`.
Other imports: `Mathlib`.
