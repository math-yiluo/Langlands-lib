# `Langlands.AnthropicFLT.P2M.Sol.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top`.

Proof (namespace `FormalGAGAFiniteLimitAux`). For an inverse system `t n : M (n+1) → M n`:
`exists_partial`, `update_compat` and `exists_forall_eq_of_surjective` show that, when all `t n` are
surjective, every `y : M n` is the `n`-th component of a compatible family; `eq_of_eq_of_le` says that
compatible families agreeing at `m` agree below `m`. `span_range_apply_eq_top`: if compatible families
`g i` span `M 0`, their `n`-th components span `M n` (Nakayama-type induction using
`I^(n+1) • M n = 0` and `ker (t n) ≤ I^(n+1) • ⊤`). The lemmas `apply_mem_of_mem_smul_top`,
`mem_smul_top_of_forall_apply_mem` and `mem_smul_top_self_iff` describe `J • ⊤` in `ι → R` and in `R`.

In the section `Engine` (`R` is `I`-adically complete), `Ψ R g k : (ι → R) → M k` is the linear
combination of the `k`-th components of the families `g i`. It is compatible with `t` (`t_Ψ`), surjective
(`Ψ_surjective`), kills coefficient vectors in `I^(k+1)` (`Ψ_eq_zero_of_forall_mem`), and a solution at
level `k` can be corrected by a vector in `I^(k+1)` to a solution at level `k+1` (`exists_step`).
Completeness turns these corrections into a convergent sequence: `exists_forall_Ψ_eq` gives a coefficient
vector `c` with `Ψ R g k c = x k` for all `k` and `c - c₀ ∈ I^(n+1)`.

`solution`: choose compatible lifts `g i` of a finite generating family of `M 0`. Their linear combination
map `Φ : (Fin r → R) → ∀ n, M n` has range `L` (by `exists_forall_Ψ_eq`), so `L` is finite. Surjectivity of
`L → M n` is `exists_forall_eq_of_surjective`. If `x n = 0`, `exists_forall_Ψ_eq` with `c₀ = 0` writes `x`
as `Φ c` with `c ∈ I^(n+1) • ⊤`, so `x ∈ I^(n+1) • L`; conversely `I^(n+1) • L` maps into
`I^(n+1) • M n = 0`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.Ψ`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.exists_partial`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.update_compat`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.exists_forall_eq_of_surjective`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.eq_of_eq_of_le`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.span_range_apply_eq_top`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.apply_mem_of_mem_smul_top`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.mem_smul_top_of_forall_apply_mem`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.mem_smul_top_self_iff`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.t_Ψ`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.Ψ_surjective`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.Ψ_eq_zero_of_forall_mem`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.exists_step`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.FormalGAGAFiniteLimitAux.exists_forall_Ψ_eq`
- theorem `P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
