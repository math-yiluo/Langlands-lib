# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Herbrand's function and the upper numbering for a group acting on a local ring (namespace `IsLocalRing`,
`R` a local ring with a `MulSemiringAction` of a group `G`; `G_i` denotes `lowerRamificationGroup R G i` of
`Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup`).

- `lowerRamificationCard R G i := Nat.card (lowerRamificationGroup R G i)`, positive for finite `G`
  (`lowerRamificationCard_pos`, `one_le_lowerRamificationCard_cast`), equal to `1` for a subsingleton `G`.
- `herbrandPhi R G : ℚ → ℚ`: `herbrandPhi R G u = u` for `u ≤ 0`, and for `u > 0`
  `herbrandPhi R G u = (∑ i ∈ Icc 1 ⌊u⌋₊, |G_i| + (u - ⌊u⌋₊) · |G_{⌊u⌋₊+1}|) / |G_0|`
  (`herbrandPhi_of_nonpos`, `herbrandPhi_of_pos`); here `|·|` is `Nat.card`, which is `0` for an infinite
  group, and division by `0` gives `0`. For finite `G` and `u ≥ 0` this is Serre's
  `φ(u) = ∫₀ᵘ dt / (G_0 : G_t)` with `G_t = G_{⌈t⌉}` (Local Fields, IV §3), a piecewise linear function with
  slope `|G_{m+1}| / |G_0|` on `[m, m+1]`. Lemmas: `herbrandPhi_zero`, `herbrandPhi_natCast`
  (`φ(n) = (∑ i ∈ Icc 1 n, |G_i|) / |G_0|`), `herbrandPhi_nonneg`, and for finite `G`: `herbrandPhi_pos`,
  `herbrandPhi_strictMono`, `herbrandPhi_monotone`, `herbrandPhi_injective` and `exists_natCast_le_herbrandPhi`
  (every `v` is bounded by some `φ(n)`).
- `herbrandPsi R G := Function.invFun (herbrandPhi R G)`: a chosen preimage under `φ` where one exists, and
  otherwise an arbitrary value. Only for finite `G` is it shown to be an inverse: `herbrandPsi_herbrandPhi`
  (`ψ (φ u) = u`) and `herbrandPsi_zero` assume `Finite G`, and the right-inverse property, also for finite `G`,
  is in `Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi`.
- `upperRamificationIndex R G v := sInf {n : ℕ | v ≤ herbrandPhi R G n}` and
  `upperRamificationGroup R G v := lowerRamificationGroup R G (upperRamificationIndex R G v)` for `v : ℚ`. The
  infimum is the natural-number `sInf`, which is `0` when the set is empty. For finite `G` the set is nonempty
  (`exists_natCast_le_herbrandPhi`), so then the upper group `G^v` is `G_n` for the least natural `n` with
  `v ≤ φ(n)`, and this index is `⌈ψ(v)⌉₊` (`upperRamificationIndex_eq_ceil_herbrandPsi` in the `…Psi` file),
  the classical `G^v = G_{ψ(v)}` for `v ≥ 0`. For infinite `G` the set can be empty: for an infinite group
  acting trivially every lower group has `Nat.card` equal to `0`, so `φ(n) = 0` for all `n`, no `n` satisfies
  `1 ≤ φ(n)`, and the index of `v = 1` is `0`. For every `v ≤ 0` and every `G` the index is `0` and `G^v = G_0`
  (`upperRamificationGroup_of_nonpos`); the
  definition does not produce the classical `G^v = G` for `v ≤ -1`. Lemmas: `upperRamificationIndex_of_nonpos`,
  `upperRamificationIndex_zero`, `mem_upperRamificationGroup`, `upperRamificationGroup_zero`,
  `upperRamificationGroup_zero_eq_ker`, `upperRamificationGroup_le_zero`, and for finite `G`:
  `le_herbrandPhi_upperRamificationIndex`, `upperRamificationIndex_le`, `upperRamificationIndex_monotone`,
  `upperRamificationGroup_antitone`, `upperRamificationIndex_herbrandPhi_natCast` and
  `upperRamificationGroup_herbrandPhi_natCast` (`G^{φ(n)} = G_n`).
- The Prop-valued definition `UpperRamificationQuotientCompat R G S H`, for a local ring `S`, a normal subgroup
  `H` of `G` and a `MulSemiringAction (G ⧸ H) S`: for every rational `v ≥ 0`,
  `(upperRamificationGroup R G v).map (QuotientGroup.mk' H) = upperRamificationGroup S (G ⧸ H) v`. This is the
  shape of Herbrand's theorem `G^v H / H = (G/H)^v` (Serre, Local Fields, IV §3, Proposition 14) when `S` is the
  ring of `H`-invariants; the definition itself allows any `S` and any action.
- Wrappers for a valuation subring `A` of `L` over `K` (namespace `ValuationSubring`): `A.herbrandPhi K`,
  `A.herbrandPsi K`, `A.upperRamificationGroup K` for the decomposition subgroup, with `herbrandPhi_zero`,
  `upperRamificationGroup_zero` (`= A.inertiaSubgroup K`), `upperRamificationGroup_le_inertiaSubgroup` and
  `upperRamificationGroup_antitone`.

Section `Gates` contains 5 `example` checks of the definitions. The file ends with 9 `#guard_msgs in #print axioms` checks (kept from FLT), for `IsLocalRing.herbrandPhi`, `IsLocalRing.herbrandPhi_strictMono`, `IsLocalRing.herbrandPsi_herbrandPhi`, `IsLocalRing.upperRamificationGroup`, `IsLocalRing.upperRamificationGroup_zero_eq_ker`, `IsLocalRing.upperRamificationGroup_antitone`, `IsLocalRing.upperRamificationGroup_herbrandPhi_natCast`, `IsLocalRing.UpperRamificationQuotientCompat`, `ValuationSubring.upperRamificationGroup_zero`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `IsLocalRing.lowerRamificationCard`
- theorem `IsLocalRing.lowerRamificationCard_pos`
- theorem `IsLocalRing.one_le_lowerRamificationCard_cast`
- theorem `IsLocalRing.lowerRamificationCard_of_subsingleton`
- def `IsLocalRing.herbrandPhi`
- theorem `IsLocalRing.herbrandPhi_of_nonpos`
- theorem `IsLocalRing.herbrandPhi_zero`
- theorem `IsLocalRing.herbrandPhi_of_pos`
- theorem `IsLocalRing.herbrandPhi_natCast`
- theorem `IsLocalRing.herbrandPhi_nonneg`
- theorem `IsLocalRing.herbrandPhi_pos`
- theorem `IsLocalRing.herbrandPhi_strictMono`
- theorem `IsLocalRing.herbrandPhi_monotone`
- theorem `IsLocalRing.herbrandPhi_injective`
- theorem `IsLocalRing.exists_natCast_le_herbrandPhi`
- def `IsLocalRing.herbrandPsi`
- theorem `IsLocalRing.herbrandPsi_herbrandPhi`
- theorem `IsLocalRing.herbrandPsi_zero`
- def `IsLocalRing.upperRamificationIndex`
- def `IsLocalRing.upperRamificationGroup`
- theorem `IsLocalRing.upperRamificationIndex_of_nonpos`
- theorem `IsLocalRing.upperRamificationIndex_zero`
- theorem `IsLocalRing.mem_upperRamificationGroup`
- theorem `IsLocalRing.upperRamificationGroup_of_nonpos`
- theorem `IsLocalRing.upperRamificationGroup_zero`
- theorem `IsLocalRing.upperRamificationGroup_zero_eq_ker`
- theorem `IsLocalRing.upperRamificationGroup_le_zero`
- theorem `IsLocalRing.le_herbrandPhi_upperRamificationIndex`
- theorem `IsLocalRing.upperRamificationIndex_le`
- theorem `IsLocalRing.upperRamificationIndex_monotone`
- theorem `IsLocalRing.upperRamificationGroup_antitone`
- theorem `IsLocalRing.upperRamificationIndex_herbrandPhi_natCast`
- theorem `IsLocalRing.upperRamificationGroup_herbrandPhi_natCast`
- def `IsLocalRing.UpperRamificationQuotientCompat`
- def `ValuationSubring.herbrandPhi`
- def `ValuationSubring.herbrandPsi`
- def `ValuationSubring.upperRamificationGroup`
- theorem `ValuationSubring.herbrandPhi_zero`
- theorem `ValuationSubring.upperRamificationGroup_zero`
- theorem `ValuationSubring.upperRamificationGroup_le_inertiaSubgroup`
- theorem `ValuationSubring.upperRamificationGroup_antitone`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup`.
Other imports: `Mathlib`.
