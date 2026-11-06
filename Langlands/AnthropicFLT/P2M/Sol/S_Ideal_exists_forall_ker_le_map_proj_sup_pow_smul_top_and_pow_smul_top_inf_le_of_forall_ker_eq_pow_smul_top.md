# `Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- `p2m_export` also exports from namespaces that contain only private declarations of this module (`ArPkg29`), which Lean does not register as namespaces; Lean's `export` rejects them, so each of them is registered by an empty block `namespace N end N` right after the options.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `ArPkg29`). Section `Adic`: for an adic system (`φ n` surjective with kernel `J^(n+1) • ⊤`),
`J^(n+1)` kills `F n` and the induced maps on quotients by a compatible family of submodules `N n`
(`(N (n+1)).map (φ n) = N n`) have kernel inside `J^(n+1) • ⊤` (`ker_mapQ_le`). Section `Engine`:
`exists_forall_pow_smul_top_inf_le` gives an Artin–Rees constant for such a compatible family `N`, by the
ported theorem `Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top`
applied to the quotient maps `G n → G n ⧸ N n`.

Section `Stable` (Mittag-Leffler argument for the kernels of `u`): `E j n` is the image in `F n` of
`ker (u (n+j))` under the transition maps (`E_zero`, `E_succ`); it decreases in `j` and lies in `ker (u n)`.
With `c` the Artin–Rees constant for the ranges of `u` in `P` (from `Engine`, since the ranges are a compatible
family by surjectivity of `φ`), `ker (u n) ≤ (ker u (n+1)).map (φ n) ⊔ J^(k+1) • ⊤` for `k + c ≤ n`
(`ker_le_map_ker_sup`), hence `ker (u n) ≤ E j n ⊔ J^(k+1) • ⊤` for all `j` (`ker_le_E_sup`); taking `k = n` and using that `J^(n+1)` kills `F n`, the images stabilise:
`E (j+1) n = E j n` for `j ≥ c` (`E_le_succ_sup`, `E_succ_eq`), so the family `E c` is compatible (`map_E_eq`). A compatible family `N ≤ ker u` lies in the
projections of `K` (`le_map_proj_K`): an element `y ∈ N n` is extended to a compatible sequence `fam` (by
`drop` below level `n` and lifting through `N` above it, `liftN`), which lies in `K` by `hK`. The projections
of `K` also form a compatible family (`map_proj_K_eq`, `map_proj_K_le_E`). `solution`: with `c₁` from the
ranges of `u` and `c₂` from `Engine` applied to the projections of `K`, the constant `c₁ + c₂` gives both
conclusions.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private theorem `ArPkg29.range_eq_top`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.map_pow_smul_top`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.pow_succ_smul_top_eq_bot`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.pow_smul_top_eq_bot_of_lt`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.ker_mapQ_le`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.exists_forall_pow_smul_top_inf_le`
- def `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E_zero`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E_succ`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.hu_apply`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.map_ker_le`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E_succ_le`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E_le_of_le`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E_le_ker`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.ker_le_map_ker_sup`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E_le_succ_sup`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.ker_le_E_sup`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.E_succ_eq`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.map_E_eq`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.map_proj_K_eq`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.map_proj_K_le_E`
- def `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.drop`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.drop_self`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.drop_compat`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.drop_mem`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.exists_lift`
- def `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.liftN`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.liftN_spec`
- def `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.fam`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.fam_of_le`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.fam_mem`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.fam_compat`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.fam_self`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.ArPkg29.le_map_proj_K`
- theorem `ArPkg29.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
