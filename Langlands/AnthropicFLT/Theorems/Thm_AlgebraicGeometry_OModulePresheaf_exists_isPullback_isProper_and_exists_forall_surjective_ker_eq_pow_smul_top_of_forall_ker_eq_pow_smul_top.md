# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.solution I q i g K' U hU T' hT' F hFc hFq φ hφs hφk hFZ F' φ' η hηs hηV hηU hηφ hβ v hvη W R L pr hprc hpri hprs hprk`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top`.
Data: `A` noetherian with an ideal `I`; `q : P ⟶ Spec A` proper; a closed immersion `i : Z ⟶ P`; a proper
`g : V' ⟶ Z` with an ordered affine cover `K'`; an open `U` of `Z` over which `g` is an isomorphism and a
closed `T'` of `P` containing the image of `Z \ U` (hypotheses `hU`, `hT'`); an inverse system of coherent,
quasi-coherent FLT presheaves `F k` on `P` with affine-indexed maps `φ k : F (k+1) → F k` that are
surjective with kernel `I^(k+1) • ⊤` on affine opens and with `F k` annihilated by the ideal of `i`; FLT
presheaves `F' k` on `V'` over `(g ≫ i) ≫ q` with maps `φ' k`; linear maps
`η k U₀ V : F k (U₀) → F' k (V)` for affine `U₀`, `V` with `V ≤ (g ≫ i)⁻¹ U₀`, semilinear (`hηs`),
compatible with restrictions in `V` and in `U₀` (`hηV`, `hηU`) and with `φ`, `φ'` (`hηφ`), and such that
`Γ(V', V) ⊗ F k (U₀) → F' k (V)`, `1 ⊗ x ↦ η x`, is an isomorphism (`hβ`); maps `v k` into the Čech
pushforward with components `η` (`hvη`). Finally an affine open `W` of `P`, a `Γ(P, W)`-algebra `R`, and a
module `L` over `Γ(P, W)` and `R` (scalar tower), finite over `R`, with surjective maps
`pr n : L → F n (W)` compatible with `φ`, jointly injective, and with kernel `(I Γ(P, W))^(n+1) • L`.

Conclusion: there are a scheme `Y`, a proper `sY : Y ⟶ Spec R` and `t : Y ⟶ V'` forming a pullback square
of `g ≫ i` along `Spec R → Spec Γ(P, W) ≅ W → P`, with `t⁻¹ V` affine for every affine `V ≤ (g ≫ i)⁻¹ W`;
and a coherent, quasi-coherent FLT presheaf `G` over `sY` with `R`-linear maps `ε U : L → G (U)` compatible
with restriction and inducing isomorphisms `Γ(Y, U) ⊗[R] L ≃ G (U)` on affine opens, and additive maps
`θ n V h : G (t⁻¹ V) → F' n (V)` that are `Γ(V', V)`-semilinear, compatible with restriction in `V` and with
`φ' n`, satisfy `θ n V h (ε x) = η n W V h (pr n x)`, are surjective, and have kernel
`(I R)^(n+1) • G (t⁻¹ V)`.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
