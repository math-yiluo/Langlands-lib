# `Langlands.AnthropicFLT.P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_FixedPoints_isDiscreteValuationRing_subring.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring`.

Auxiliary namespace `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.HerbrandPortV`.

- `prod_smul_mem_subring`: the norm `∏ h : H, h • x` is `H`-fixed; `exists_mem_subring_addVal_pos`: the norm of a
  uniformizer is a nonzero fixed element of positive valuation.
- `mem_subring_of_mul_mem`: if `t` is fixed and nonzero and `t * c` is fixed, then `c` is fixed;
  `exists_addVal_eq_natCast`: nonzero elements have finite valuation.
- `isDiscreteValuationRing_subring`: let `m` be the least positive valuation of a fixed element and `t` a fixed
  element with `addVal R t = m`. Every fixed nonzero nonunit has valuation at least `m`. A fixed nonzero `s` with
  `addVal R s = v` is `t ^ (v / m) * c` with `c` fixed (divisibility in `R` and `mem_subring_of_mul_mem`), and `c`
  is a unit, since otherwise `addVal R c ≥ m` would contradict `v - (v / m) m < m`. `t` is irreducible in the fixed
  subring (a product of two nonunits would have valuation at least `2m`; units are detected in `R` by
  `FixedPoints.isUnit_subring_iff`), so `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization` applies.

`solution` is `HerbrandPortV.isDiscreteValuationRing_subring`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.HerbrandPortV.prod_smul_mem_subring`
- theorem `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.HerbrandPortV.exists_mem_subring_addVal_pos`
- theorem `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.HerbrandPortV.mem_subring_of_mul_mem`
- theorem `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.HerbrandPortV.exists_addVal_eq_natCast`
- theorem `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.HerbrandPortV.isDiscreteValuationRing_subring`
- theorem `P2MW.S_FixedPoints_isDiscreteValuationRing_subring.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`.
Other imports: `Mathlib`.
