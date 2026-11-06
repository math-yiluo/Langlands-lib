# `Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system`.

Proof (namespace `E29AL`). `limSub E τ` is the submodule of compatible families of `∏ E k` (the inverse limit);
a compatible family vanishing at level `N` vanishes below `N` (`apply_eq_zero_of_le`); every element of `E k`
lies in a compatible family (`exists_mem_apply_eq`, by surjectivity of the `τ`); and an element of
`span(g) • N` is a sum `∑ g i • v i` with `v i ∈ N` (`exists_sum_of_mem_span_smul`).

`solution` takes `L := limSub E τ`; membership and surjectivity of the projections are immediate. The kernel of
the `n`-th projection contains `I^(n+1) • ⊤` because `I^(n+1)` kills `E n` (`hsup`). Conversely, let `x ∈ L` have
`x n = 0` and let `g : Fin s → R` generate `I^(n+1)` (`I` is finitely generated). Then `x (n+1) ∈ span(g) • ⊤`,
which gives families `l i ∈ L` with `x - ∑ g i • l i` vanishing at level `n+1` (`init`). Inductively (`step`),
if `x - ∑ g i • l i` vanishes at level `n+d+1`, its level `n+d+2` component lies in
`span(g) • I^(d+1) • ⊤`, so the `l i` can be corrected by elements of `I^(d+1) • L` (which vanish at level `d`)
to make it vanish one level higher. The corrected families stabilise levelwise (`hstat`), their limits `Y i`
lie in `L`, and `x = ∑ g i • Y i ∈ I^(n+1) • L`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.E29AL.limSub`
- theorem `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.E29AL.mem_limSub`
- theorem `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.E29AL.apply_eq_zero_of_le`
- theorem `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.E29AL.exists_mem_apply_eq`
- theorem `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.E29AL.exists_sum_of_mem_span_smul`
- theorem `P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
