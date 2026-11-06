# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `CokerAdic29`). Section `LinAlg`: `descend` factors a linear map `g` through a surjection `f`
with `ker f ≤ ker g` (`descend_apply`, `descend_comp`). `solution`: at each level `k` the ported theorem
`AffHom.exists_isQuasicoherent_surjective_ker_eq_range` applied to `u k` gives a coherent quasi-coherent
cokernel `Cs k` with a surjection `θ k : AffHom (Ps k) (Cs k)` whose kernel on affines is the range of
`u k`. Section `Main`: since `π k ∘ u (k+1) = u k ∘ φ k` (`huc`), `θ k ∘ π k` kills the kernel of
`θ (k+1)` (`ker_le`), so it descends to `gamma k : AffHom (Cs (k+1)) (Cs k)` with
`gamma k ∘ θ (k+1) = θ k ∘ π k` (`gamma_comp`; naturality is inherited). `gamma k` is surjective because `θ k`
and `π k` are (`gamma_surjective`). Its kernel: using surjectivity of `φ k`, the kernel of `θ k ∘ π k` is
`range (u (k+1)) ⊔ ker (π k)` (`ker_comp_eq`); its image under `θ (k+1)` is `θ (k+1)(I^(k+1) • ⊤)`, which is
`I^(k+1) • ⊤` by surjectivity (`ker_gamma`). `solution` assembles `Cs`, `gamma`, `θ` and these facts.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.descend`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.descend_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.descend_comp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.ker_le`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.gamma`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.gamma_app_theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.gamma_comp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.gamma_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.ker_comp_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.CokerAdic29.ker_gamma`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range` (same contribution).
Other imports: `Mathlib`.
