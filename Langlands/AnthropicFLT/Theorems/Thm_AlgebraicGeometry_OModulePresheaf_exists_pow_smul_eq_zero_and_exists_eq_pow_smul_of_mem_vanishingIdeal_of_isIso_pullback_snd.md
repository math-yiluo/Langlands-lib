# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd.solution I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk sY t hY hta G hGc hGq ε hεr hεβ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd`.
The hypotheses `I` through `hprk` are those of the ported theorem `AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top` (same names and types; its
Markdown lists them; among them `hU`: `g` is an isomorphism over `U`, and `hT'`: `T'` contains the image of
`Z \ U`). In addition: `Y`, a proper `sY : Y ⟶ Spec R` and `t : Y ⟶ V'` with the pullback square `hY` and affine
preimages `hta`; and a coherent, quasi-coherent `G` over `sY` with `R`-linear maps `ε U : L → G (U)` (`hεr`,
`hεβ`: `ε` induces `Γ(Y, U) ⊗[R] L ≃ G (U)` on affine opens).

Conclusion: for every `a` in the ideal over `W` of the vanishing ideal sheaf of `T'`, with
`chart j := K'.U j ⊓ (g ≫ i)⁻¹ W`: (1) every `x : L` with `ε (t⁻¹ (chart j)) x = 0` for all `j` is killed by a
power of `a`; (2) for every family `c j : G (t⁻¹ (chart j))` whose restrictions to pairwise intersections
agree, there are `k` and `x : L` with `ε (t⁻¹ (chart j)) x = aᵏ • c j` for all `j`.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd` (same contribution).
Other imports: `Mathlib`.
