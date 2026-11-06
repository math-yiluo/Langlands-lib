# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq.solution q GE hGEc hGEq GK hGKc hGKq X hXc hXq εX hXf K rk pr hpr δ hδ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq`: under the
hypotheses of the ported theorem `exists_overlapIso_extPushout_of_forall_res_symm_mk_eq` up to the chart data
(`q` separated with `P` locally noetherian, `GE`, `GK` coherent quasi-coherent, a model `X` of `Ext¹(GE, GK)` with
`εX`, `hXf`, an ordered affine cover `K` with presentations `pr i` and maps `δ i` whose classes agree on overlaps),
there are chart data for every chart `i` as in the ported theorem `exists_chartModel_extPushout_of_surjective`
(restricted presentations `prU i U`, kernel maps `gU i U`, maps `δU i U`, pushout extensions
`ExtPushout (prU i U) (δU i U)` with semilinear functorial restriction maps `res i` satisfying the localization
conditions `hqc`, finite over `Γ(P, U)`, exact sequences `0 → GK(U) →ϑ ExtPushout →θE GE(U) → 0` compatible with
restriction, `ϑ = inl`, `θE = proj`, and the action of `res` on `inl`, `inr`), together with overlap isomorphisms
`u i j W hj` between the pushout extensions of charts `i` and `j` over affine `W ⊆ U_i ∩ U_j`: bijective,
semilinear, compatible with `res`, with `ϑ` and with `θE`. (Gluing data for the global extension of `GE` by `GK`
with the given class.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_LinearMap_ExtPushout` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq` (same contribution).
Other imports: `Mathlib`.
