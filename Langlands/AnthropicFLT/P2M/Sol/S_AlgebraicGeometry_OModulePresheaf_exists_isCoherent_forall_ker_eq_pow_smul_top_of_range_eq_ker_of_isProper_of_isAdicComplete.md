# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete`.

Proof. Namespaces `C5vAux`, `C5vAux2`: extensionality and composition for `AffHom`, and restriction of scalars from
`Γ(P, U)` to `A` for kernels, ranges and `J^n • ⊤` with `J = I Γ(P, U)` (`restrictScalars_map_pow_smul_top`,
`restrictScalars_ker`, `restrictScalars_range`, `appSections_restrictScalars`). Namespace `C5v`: two compatible
families of maps into an adic system `E` that agree after the maps `u` (with `range u = ker θ` and the shift bound)
are equal (`eq_of_compatible_of_apply_eq`, `eq_of_compatible_of_comp_eq`, by the uniqueness part of the ported
theorem `Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul`).

`solution`. (1) The compatible maps `θ k ∘ ψP k : GP → Cs k` lift through the adic system `ψC` of `GC`: by the ported
theorem `existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper` there is `ρ : AffHom GP GC` with
`ψC k ∘ ρ = θ k ∘ ψP k`. (2) The ported theorem `AffHom.exists_isQuasicoherent_injective_range_eq_ker` gives the
coherent quasi-coherent kernel `G` of `ρ` with inclusion `ιG`. (3) On each affine `U`, the module-level ported
theorem `Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`, applied over the noetherian
ring `Γ(P, U)` to `ρ`, `ιG` and the section maps of all the systems, gives surjections `ψU k : G(U) → E k (U)` with
kernel `J^(k+1) • ⊤ = I^(k+1) • ⊤`, compatible with `τ` and with `u k ∘ ψU k = ψP k ∘ ιG`. (4) Naturality of the `ψU`
in `U` (`hnat`) follows from `C5v.eq_of_compatible_of_comp_eq`, since both composites with restriction are
compatible families with the same image under `u`. The `ψU` therefore assemble to `ψ k : AffHom G (E k)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5vAux.affHom_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5vAux.affHom_comp_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5vAux.restrictScalars_map_pow_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5vAux.restrictScalars_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5vAux.restrictScalars_range`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5v.eq_of_compatible_of_apply_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5v.eq_of_compatible_of_comp_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.C5vAux2.appSections_restrictScalars`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker` (same contribution).
Other imports: `Mathlib`.
