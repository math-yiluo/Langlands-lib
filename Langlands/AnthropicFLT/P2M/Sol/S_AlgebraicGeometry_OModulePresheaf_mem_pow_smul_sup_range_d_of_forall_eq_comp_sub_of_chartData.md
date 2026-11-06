# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData`.

Proof. Helpers (`Y1DSol`, as in the neighbouring ports): `isLocallyNoetherian_of_isProper`, `pi_mem_smul_top`,
`mem_pow_smul_top_iff_of_isScalarTower`, and the identification `topEquiv` of sections of the internal Hom over an
affine with module homomorphisms (`evalTop`, `evalTop_apply`, `evalTop_bijective`, `topEquiv_apply`), compatible
with `I`-adic membership (`mem_pow_smul_top_of_top`).

`solution`: the ported theorem `exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData` gives
`1`-cochains `t m` comparing the chart maps `θF`. For a `2`-simplex `s`, expanding `d (t m) s` over the three faces
(`d_apply`) and using the identities for `g` and `t m` (and `hc2`) shows `lam m ∘ (g s − d (t m) s) = 0` on the
triple intersection (`tri`). By the Artin–Rees bound `hlami` for `lam` and the ported theorem
`LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul` for `Hom(GE, GK)` on that affine, there is `C s`
with `g s − d (t m) s ∈ I^(n'+1)` for `m ≥ n' + C s` (`perS`). With `Cmax` the maximum over the finitely many
simplices, `g = (g − d (t (n + Cmax))) + d (t (n + Cmax))` lies in `I^(n+1) • ⊤ + range d`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.isLocallyNoetherian_of_isProper`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.pi_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.mem_pow_smul_top_iff_of_isScalarTower`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.evalTop`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.evalTop_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.evalTop_bijective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.topEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.topEquiv_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.Y1DSol.mem_pow_smul_top_of_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq` (same contribution).
Other imports: `Mathlib`.
