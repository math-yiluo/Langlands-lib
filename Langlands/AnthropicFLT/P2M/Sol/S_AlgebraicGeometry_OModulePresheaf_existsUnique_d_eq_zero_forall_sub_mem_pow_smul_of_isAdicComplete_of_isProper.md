# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper`;
it is `FF0LimAux.main`.

Proof (namespace `FF0LimAux`). Section `Algebra`: `coe_mem_smul_iff` compares `J • p` in `M` and in the
submodule `p`; `pow_smul_le_pow_smul` is antitonicity of `I^n • N`; `env c` is a monotone function with
`n + c n ≤ env c n` and `n ≤ env c n` (`add_le_env`, `env_mono`, `le_env`). Section `Main`:
`sub_mem_of_le`, `sub_mem_of_le_of_le` give `t m - t n ∈ I^(n+1) • ⊤` for `n ≤ m` from the hypothesis on
successive differences.

`main`: `H⁰ = F.H0 K` is a finite `A`-module (ported `cechFinite_of_isProper`), hence `I`-adically complete
(ported `IsAdicComplete.of_finite_of_isNoetherianRing`). For each `n`, the ported theorem
`exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper` gives a cocycle `a n` with `t (k n) - a n ∈ I^n • ⊤`
for some `k n ≥ n`, and the ported Artin–Rees theorem `exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper`
gives `c₂ n` with `H⁰ ∩ I^(n + c₂ n) • ⊤ ≤ I^n • H⁰`. Then `b n := a (env c₂ n)` is a Cauchy sequence in
`H⁰` for the `I`-adic topology, so it has a limit `L` by completeness, and `L` satisfies
`L - t n ∈ I^(n+1) • ⊤` for every `n`. Uniqueness: the difference `δ` of two such cocycles lies in `H⁰` and
in every `I^m • ⊤`, hence (Artin–Rees again) in every `I^m • H⁰`, and is `0` because the finite module `H⁰`
over the complete noetherian ring is `I`-adically Hausdorff.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.coe_mem_smul_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.pow_smul_le_pow_smul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.env`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.add_le_env`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.env_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.le_env`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.sub_mem_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.sub_mem_of_le_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.FF0LimAux.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library), `Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing` (same contribution).
Other imports: `Mathlib`.
