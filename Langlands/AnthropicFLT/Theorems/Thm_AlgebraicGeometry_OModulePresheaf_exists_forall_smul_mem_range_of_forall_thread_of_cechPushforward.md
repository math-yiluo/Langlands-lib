# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.solution I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ G' hG'c hG'q ψ' hψ's hψ'k hψ'c v hvη Ps hPsc hPsq π hπs hπk ψP hψPs hψPk hψPc ν hνc hνψP hνi u huc hνu hunif`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward`.
The hypotheses `I` through `hβ` are those of the ported theorem `AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top` (same names and types; its Markdown
lists them), as are `v` and `hvη`. In addition: a coherent quasi-coherent presheaf `G'` over the composite
`(g ≫ i) ≫ q` with surjections `ψ' k : G' → F' k` on affines, of kernel `I^(k+1) • ⊤`, compatible with `φ'`
(so `F'` is the adic system of `G'`); a coherent quasi-coherent adic system `Ps` on `P` (transition maps `π`)
with surjections `ψP k` from the Čech pushforward of `G'` onto `Ps k` of kernel `I^(k+1) • ⊤` compatible with
`π`; maps `ν k : Ps k → cechPushforward (F' k)` compatible with `π` and `φ'`, with `ν k ∘ ψP k` the Čech
pushforward of `ψ' k` and with kernel of `ν (k+c)` inside `I^(k+1) • ⊤` for some `c` (`hνi`); maps
`u k : F k → Ps k` compatible with `φ` and `π` and with `ν k ∘ u k = v k`; and a uniform bound `hunif`: there is
`N` such that on every affine `W`, every compatible family of Čech sections multiplied by an element `a` of the
`N`-th power of the vanishing ideal of `T'` over `W` comes from a thread in `F`, and such `a` kill every thread
of `F` killed by `v`.

Conclusion: there is `N` such that on every affine `W` and for every `a` in the `N`-th power of the vanishing
ideal of `T'` over `W`, `a • y` lies in the range of `u k` for every `y ∈ Ps k (W)`, and there is `c` (depending
on `W`) such that `a • x ∈ I^(k+1) • ⊤` whenever `u (k+c) x = 0`.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward` (same contribution).
Other imports: `Mathlib`.
