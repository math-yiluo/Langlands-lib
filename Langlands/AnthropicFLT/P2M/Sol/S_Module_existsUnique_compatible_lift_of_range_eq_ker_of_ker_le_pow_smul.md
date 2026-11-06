# `Langlands.AnthropicFLT.P2M.Sol.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.solution` proves the
statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul`.

Proof (a single tactic proof). On the products `∏ E k` and `∏ P k` let `T` and `S` be the shift operators
`(T x) k = τ k (x (k+1))`, `(S y) k = π k (y (k+1))`, and `U` the componentwise map `u`; then `U ∘ T = S ∘ U`.
Since `τ k` is surjective with kernel `I^(k+1) • ⊤`, `I^(k+1)` kills `E k` (`hkill`). With `c` from `hui`, an `x`
with `U x = 0` has `x k ∈ I^(k+1-c) • ⊤`, each application of `T` raises the exponent by one (`hinv`, `hiter`),
so `T^c x = 0` (`hvanish`). Existence: choose `e' k` with `u k (e' k) = p k` (possible since `θ k (p k) = 0` and
`range u k = ker θ k`); then `U (T e' - e') = S p - p = 0`, so `T^c (T e') = T^c e'`, i.e. `e := T^c e'` is a
compatible family with `U e = S^c p = p`. Uniqueness: the difference `d` of two solutions satisfies `T d = d` and
`U d = 0`, so `d = T^c d = 0`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
