# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.solution` proves
the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top`.

Proof. Helpers (`E29EA`): a map from a free module with values in the image of `s` factors through `s`
(`exists_comp_eq_of_forall_mem_range`), and `exists_lifts` builds, by recursion on `n` and freeness of `B^r`,
compatible lifts `ℓ n : B^r → F n` of `ψE n ∘ p` along the surjections `ε n`
(`ε n ∘ ℓ n = ψE n ∘ p`, `φ n ∘ ℓ (n+1) = ℓ n`).

`solution`: take `ℓ` from `exists_lifts`, `c` from `hlami`, `c₁` from the ported theorem
`LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp` and `c₂` from the ported theorem
`LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul` (both for `Hom(ker p, GK)`). `J^(n+1)` kills `F n`,
so `J^(n+1) GK ⊆ ker (lam n)`; `ℓ m` maps `ker p` into `ker (ε m) = range (lam m)`; transition maps carry `lam` and
`ℓ` from level `N` down to level `n` (`descend`). With `N n = n + c₂ + c₁ + 1 + c`, the kernel of `lam (N n)` lies in
`J^(n+1+c₂+c₁) GK`, so `s ↦ lam (N n)⁻¹ (ℓ (N n) s)` is a well-defined map `f n : ker p → GK / J^(n+1+c₂+c₁) GK`;
the Mittag-Leffler lemma lifts it to `δs n : ker p → GK`, correct modulo `J^(n+1+c₂)`. Then
`lam n ∘ δs n = ℓ n` on `ker p` (the error lies in `J^(n+1) GK ⊆ ker lam n`), and `δs (n+1) − δs n` takes values in
`J^(n+1+c₂) GK`, so by the Artin–Rees bound it lies in `J^(n+1) • Hom(ker p, GK)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.E29EA.exists_comp_eq_of_forall_mem_range`
- theorem `P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.E29EA.exists_lifts`
- theorem `P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul` (same contribution).
Other imports: `Mathlib`.
