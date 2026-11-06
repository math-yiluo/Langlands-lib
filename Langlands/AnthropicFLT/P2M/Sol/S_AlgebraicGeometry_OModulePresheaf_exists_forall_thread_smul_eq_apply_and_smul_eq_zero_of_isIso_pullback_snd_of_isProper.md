# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper`.

Proof (namespace `W_ASM`). A "frame" over an affine open `W` is the data `L`, `pr`, `Y`, `sY`, `t`, `G`, `ε`,
`θ` with the properties of the ported theorem
`OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top`,
over `R` = the completion of `Γ(P, W)`.
- `algebraMap_smul_eq_app_appLE_smul`: on `G (t⁻¹ V)` the action of `a : Γ(P, W)` through `R` equals the action
  of its image in `Γ(Y, t⁻¹ V)`.
- `exists_frame`: frames exist. `L` is the inverse limit of the `F n (W)`, finite over the completion
  (ported `AdicCompletion.exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective`);
  the completion is complete for the extended ideal (`isAdicComplete_map_algebraMap_of_fg`); `Y`, `G`, `ε`, `θ`
  come from the ported theorem above.
- `torsion_of_frame`: for a frame there is `N` such that the Čech map `u : L → ∏ G (t⁻¹ chart j)` has kernel
  killed by `(vanishing ideal of T' over W)^N` and the compatible families are mapped into the range by that
  ideal. The compatible families form a finitely generated module and `L` maps to them (ported
  `exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper`); for each element of
  a finite generating set of the vanishing ideal the two properties hold up to powers (ported
  `exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd`), and the ported
  `Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul` gives a uniform power.
- `threads_of_torsion`: from the conclusion of `torsion_of_frame` with exponent `N`, the conclusion of the
  theorem follows over `W`: a compatible thread `ℓ` of sections of the Čech pushforwards is the image of a
  compatible family on `Y` (thread theorem above), `a • c = u x` for some `x : L`, and `m n := pr n x` works;
  for injectivity, a thread `m` with `v n (m n) = 0` comes from `x : L` (`hprt`) with `u x = 0`, so `a • x = 0`.

`solution`: given `W₀`, take a frame over `W₀` and `N` from `torsion_of_frame`. For `W ≤ W₀`, take a frame over
`W`. The restriction `Γ(P, W₀) → Γ(P, W)` is flat and of finite type (`P` locally noetherian), so the ported
`AdicCompletion.exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType` gives a flat map `f` between
the completions; the restrictions `κ n : F n (W₀) → F n (W)` are base changes (quasi-coherence, ported
`IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res`), so the ported
`AdicCompletion.exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top` gives a
bijection `e` between the base change of `L₀` and `L`. The ported
`forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective` transfers the torsion statement with
exponent `N` from `W₀` to `W`, and `threads_of_torsion` concludes.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.W_ASM.algebraMap_smul_eq_app_appLE_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.W_ASM.torsion_of_frame`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.W_ASM.threads_of_torsion`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.W_ASM.exists_frame`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_module_finite_forall_comp_eq_and_ker_eq_pow_smul_top_of_forall_surjective` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isAdicComplete_map_algebraMap_of_fg` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_and_flat_of_flat_of_finiteType` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective` (same contribution).
Other imports: `Mathlib`.
