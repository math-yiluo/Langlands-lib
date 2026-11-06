# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective.solution I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W₀ R₀ L₀ pr₀ hprc₀ hpri₀ hprs₀ hprk₀ sY₀ t₀ hY₀ hta₀ G₀ hGc₀ hGq₀ ε₀ hεr₀ hεβ₀ W R L pr hprc hpri hprs hprk sY t hY hta G hGc hGq ε hεr hεβ hW hR e heb he N hk₀ hc₀`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective`.
The hypotheses `I` through `hvη` are those of the ported theorem `AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top` (same names and types; its Markdown
lists them). Then two copies of the remaining data of that theorem and of its conclusion are given: one over
an affine open `W₀` (`R₀`, `L₀`, `pr₀`, `hprc₀`, `hpri₀`, `hprs₀`, `hprk₀`, `Y₀`, `sY₀`, `t₀`, `hY₀`, `hta₀`, `G₀`,
`hGc₀`, `hGq₀`, `ε₀`, `hεr₀`, `hεβ₀`) and one over an affine open `W` (`R`, `L`, `pr`, …, `G`, `ε`, `hεr`, `hεβ`),
with the same meaning as there. Moreover `W ≤ W₀`, `R` is a flat `R₀`-algebra compatible with the restriction
`Γ(P, W₀) → Γ(P, W)` (`hR`), `e : R ⊗[R₀] L₀ → L` is a bijective `R`-linear map with
`pr n (e (1 ⊗ x₀)) = (pr₀ n x₀)|_W` (`he`), and `N` is a natural number such that, over `W₀` (with
`chart₀ j := K'.U j ⊓ (g ≫ i)⁻¹ W₀`): every `x : L₀` with `ε₀ (t₀⁻¹ chart₀ j) x = 0` for all `j` is killed by every
element of `(vanishing ideal of T' over W₀)^N` (`hk₀`), and for every compatible family `c` on the
`t₀⁻¹ chart₀ j` and every `a` in that ideal there is `x` with `ε₀ x = a • c j` for all `j` (`hc₀`).

Conclusion: the same two properties hold over `W` (for `L`, `ε`, the charts `K'.U j ⊓ (g ≫ i)⁻¹ W` and the ideal
`(vanishing ideal of T' over W)^N`).

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective` (same contribution).
Other imports: `Mathlib`.
