# `Langlands.AnthropicFLT.Theorems.Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.solution I E τ hτs hτk P π C θ u huc hur hui p hp hpθ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul`: let `R` be a commutative
ring with an ideal `I` and `E k` an inverse system of `R`-modules with surjective transition maps `τ k` of
kernel `I^(k+1) • ⊤`. Let `P k` be an inverse system with transition maps `π k`, `θ k : P k → C k` linear maps,
and `u k : E k → P k` compatible maps (`π k ∘ u (k+1) = u k ∘ τ k`) with `range (u k) = ker (θ k)` and, for some
`c`, `ker (u (k+c)) ≤ I^(k+1) • ⊤` for all `k`. Then for every compatible family `p k ∈ P k` with
`θ k (p k) = 0` there is a unique compatible family `e k ∈ E k` with `u k (e k) = p k` for all `k`.

The proof term applies the companion solution theorem
`P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul` (same contribution).
Other imports: `Mathlib`.
