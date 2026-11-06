# `Langlands.AnthropicFLT.Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary`

Ported by Worker 84 for the exact-target proof of
`Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement` (Brauer's induction theorem, an input of
Henniart's 2000 proof; program `34b81620-20d7-4059-9b08-6bedd1c1c029`). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.solution`; the theorem has no explicit arguments. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement (Solomon's induction theorem for the trivial character, in the form used for Brauer's theorem).
`ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary`: for a finite group `G : Type`
there are `k : ℕ`, subgroups `H : Fin k → Subgroup G` and integers `a : Fin k → ℤ` such that

- every `H i` is hyperelementary in the following sense: there are a prime `q` and a cyclic subgroup
  `C ≤ H i` with `Nat.card C` coprime to `q`, `C` stable under conjugation by `H i`, and
  `h ^ (q ^ n) ∈ C` for some `n` for every `h ∈ H i` (so `H i` is an extension of a `q`-group by a cyclic group of order prime to `q`);
- for every `g : G`, `1 = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => 1) g` in `ℚ`.

The group lives in `Type` (universe 0). The proof term applies the companion solution theorem
`P2MW.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced` and `Langlands.AnthropicFLT.P2M.Sol.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary` (same contribution).
Other imports: `Mathlib`.
