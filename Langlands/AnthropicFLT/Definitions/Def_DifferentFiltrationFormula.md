# `Langlands.AnthropicFLT.Definitions.Def_DifferentFiltrationFormula`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_DifferentFiltrationFormula.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Counting functions for the lower filtration and a Prop-valued form of Hilbert's different formula. In this port
the file is imported by `P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn` and
`Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn`, which use only the lower ramification groups
it imports; its own declarations are not used by the Herbrand theorems.

- For a local ring `B` with a `MulSemiringAction` of `G` (section `FiltrationSum`):
  `lowerRamificationFiltrationSum B G N := ∑ i ∈ range N, (Nat.card G_i - 1)` (natural-number subtraction) and
  `lowerRamificationDepthCount B G N σ := #{i ∈ range N | σ ∈ G_i}`.
- `lowerRamificationGroup_eq_bot_of_le` (`G_N = ⊥` and `N ≤ M` give `G_M = ⊥`),
  `lowerRamificationFiltrationSum_eq_of_le` and `lowerRamificationFiltrationSum_eq_of_eq_bot` (the sum no longer
  changes once `G_N = ⊥`), and, for `Fintype G` with decidable equality,
  `sum_lowerRamificationDepthCount_erase_one` (summing the counts over `σ ≠ 1` gives the filtration sum; via the
  private lemma `sum_erase_one_ite_mem`).
- For a domain `A`, a local Dedekind domain `B` and a torsion-free `A`-algebra structure on `B` (section
  `StatementLayer`): the Prop-valued definition `DifferentEqPowFiltrationSum A B G`: for every `N` with
  `G_N = ⊥`, `differentIdeal A B = (maximalIdeal B) ^ lowerRamificationFiltrationSum B G N` (the shape of Hilbert's
  formula `v_L(𝔇) = ∑_{i ≥ 0} (|G_i| - 1)`, Serre, Local Fields IV §1 Proposition 4; it is only stated here, not
  proved), and `differentEqPowFiltrationSum_of_cutoff` (it suffices to check one `N` with `G_N = ⊥`).
- The file sets `attribute [local instance] FractionRing.liftAlgebra`.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `lowerRamificationFiltrationSum`
- def `lowerRamificationDepthCount`
- theorem `lowerRamificationGroup_eq_bot_of_le`
- theorem `lowerRamificationFiltrationSum_eq_of_le`
- theorem `lowerRamificationFiltrationSum_eq_of_eq_bot`
- private theorem `sum_erase_one_ite_mem`
- theorem `sum_lowerRamificationDepthCount_erase_one`
- def `DifferentEqPowFiltrationSum`
- theorem `differentEqPowFiltrationSum_of_cutoff`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup`.
Other imports: `Mathlib.RingTheory.DedekindDomain.Different`.
