# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData`.

Proof (direct). For a `2`-simplex `s = (i₀, i₁, i₂)` and an affine `W` inside the triple intersection, the two maps
`u_{i₁i₂} ∘ u_{i₀i₁}` and `u_{i₀i₂}` from `M i₀ W` to `M i₂ W` agree on `GK` and over `GE` (by `huϑ`, `huθE`), so the
ported theorem `LinearMap.existsUnique_sub_eq_comp_comp_of_extension` gives a unique `γ s W : GE(W) → GK(W)` with
`u_{i₁i₂} ∘ u_{i₀i₁} − u_{i₀i₂} = ϑ ∘ γ s W ∘ θE`. Checking on preimages under the surjective `θE` and using
injectivity of `ϑ`, `γ s W` is `Γ(P, W)`-linear (from `hθEs`, `hϑs`, `hus`) and compatible with restriction (from
`hθEn`, `hϑn`, `hun`), so the family `W ↦ γ s W` is a section of the ported internal Hom `internalHom GE GK` over
the triple intersection; these sections form the `2`-cochain `g`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution).
Other imports: `Mathlib`.
