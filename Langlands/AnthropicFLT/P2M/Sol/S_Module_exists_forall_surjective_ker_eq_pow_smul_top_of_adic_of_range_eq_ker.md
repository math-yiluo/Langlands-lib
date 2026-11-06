# `Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.solution` proves
the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`.

Proof (a single tactic proof). `I^(k+1)` kills `E k` (`hkill`), and a compatible family whose level-`(j+c')`
component lies in `I^(j+1) • ⊤` vanishes at level `j` (`hdesc`). For `x ∈ K`, `ψP k (ι x)` is a compatible family
killed by the `θ k` (since `ρ (ι x) = 0`), so the ported theorem
`Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul` gives a unique compatible family
`Φ x` in `∏ E k` with `u k (Φ x k) = ψP k (ι x)`; uniqueness makes `Φ` linear, and `ψ k` is its `k`-th component.
Compatibility with `τ` and `u k ∘ ψ k = ψP k ∘ ι` hold by construction.

For surjectivity and the kernel, the ported theorem
`Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system` gives the inverse limit `L` of
the `E k` with surjective projections of kernel `I^(k+1) • L`. Identifying `P k` with `M / I^(k+1) M` (`eqk`),
every `e ∈ L` defines an element `Z e` of the completion `AdicCompletion I M`, which is killed by the completion
of `ρ` (`hZ2`), and `Z (Φ x)` is the image of `ι x` (`hZ3`). By the ported theorem
`AdicCompletion.map_ker_subtype_injective_and_range_eq_ker_map`, `Z e` comes from the completion of `K`
(`hZrange`). Surjectivity: for `y ∈ E k` take `e ∈ L` through `y` and `x ∈ K` approximating the preimage of `Z e`
at level `k + c + 1`; then `Φ x - e` is killed by `u (k+c)` up to `I^(k+1)`, so `hdesc` gives `ψ k x = y`. Kernel:
if `ψ k x = 0`, then `Φ x ∈ I^(k+1) • L`, so the image of `x` in the completion of `K` lies in `I^(k+1) • ⊤`
(injectivity of the completed `ι`), and evaluating at level `k+1` gives `x ∈ I^(k+1) • ⊤`; the reverse inclusion
holds because `I^(k+1)` kills `E k`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_map_ker_subtype_injective_and_range_eq_ker_map` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system` (same contribution).
Other imports: `Mathlib`.
