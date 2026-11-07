# `Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField`.

Auxiliary namespace `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM`.
The argument is Serre's (Local Fields, III §6, Proposition 12).

- `IsDiscreteValuationRing.irreducible_of_addVal_eq_one`.
- `Subalgebra.eq_top_of_irreducible_mem_of_residue_surjective`: a subalgebra `S` of a finite extension of
  discrete valuation rings `B/A` (injective algebra map) that contains a uniformizer `π` of `B` and meets every
  residue class of `B` is `⊤`. By induction every `b` is congruent to an element of `S` modulo `𝔪_Bᵏ` for every
  `k` (correct the error `πᵏ c` by `πᵏ s'` with `s' ≡ c`); taking `k = addVal B (π_A)` and Nakayama
  (`IsLocalRing.map_mkQ_eq_top`, `B` finite over `A`) gives `S = ⊤`.
- `residue_aeval_eq` and `adjoin_residue_surjective_of_adjoin_residue_eq_top` (if the residue of `x` generates the
  residue field extension, `Algebra.adjoin A {x}` meets every residue class).
- `exists_adjoin_singleton_eq_top`: take a primitive element `ᾱ` of the finite separable residue extension, a lift
  `x`, and a monic lift `G` over `A` of the minimal polynomial of `ᾱ`, with image `Φ` over `B`. Then `Φ(x) ∈ 𝔪_B` and
  `Φ'(x)` is a unit (separability). If `addVal B (Φ(x)) = 1`, `Φ(x) ∈ A[x]` is a uniformizer and `A[x] = B` by the
  subalgebra lemma. Otherwise `addVal B (Φ(x)) ≥ 2`, and for a uniformizer `π₀` the element `x' = x + π₀` has the
  same residue and `addVal B (Φ(x')) = 1` (Taylor expansion `Polynomial.binomExpansion`), so `A[x'] = B`.

`solution` applies `exists_adjoin_singleton_eq_top`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM.IsDiscreteValuationRing.irreducible_of_addVal_eq_one`
- theorem `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM.Subalgebra.eq_top_of_irreducible_mem_of_residue_surjective`
- theorem `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM.IsDiscreteValuationRing.residue_aeval_eq`
- theorem `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM.IsDiscreteValuationRing.adjoin_residue_surjective_of_adjoin_residue_eq_top`
- theorem `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM.IsDiscreteValuationRing.exists_adjoin_singleton_eq_top`
- theorem `P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`.
Other imports: `Mathlib`.
