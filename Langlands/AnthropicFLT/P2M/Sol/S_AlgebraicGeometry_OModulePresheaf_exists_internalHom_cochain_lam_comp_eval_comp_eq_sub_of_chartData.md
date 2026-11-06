# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData`.

Proof (namespace `Y2bSol`). `P` is locally noetherian (`isLocallyNoetherian_of_isProper`). General facts: tuples of
elements of `J • N_s` lie in `J • ∏ N_s` (`pi_mem_smul_top`), `I`-adic membership agrees over `A` and over an
`A`-algebra (`mem_pow_smul_top_iff_of_isScalarTower`); for coherent quasi-coherent `F`, `G` and affine `U`,
evaluation at `U` identifies sections of the ported internal Hom over `U` with `Hom_{Γ(U)}(F(U), G(U))`
(`evalTop`, `evalTop_apply`, `evalTop_bijective`, `topEquiv`, `topEquiv_apply`, `topEquiv_symm_top`, `ext_of_top`),
compatibly with `I`-adic membership (`mem_pow_smul_top_of_top`). Frame: `I^(k+1)` kills `F k`
(`pow_smul_top_eq_bot`), and iterated transition maps `phiIter` commute with `lam` and `θF` (`phiIter_lam`,
`phiIter_θF`).

`exists_top`: on the affine overlap of a `1`-simplex `s = (i₀, i₁)`, the two compatible families `θF i₀` and
`θF i₁ ∘ u_{i₀i₁}` both extend `lam` and agree after `ε` (by `hc2`, `hc3`, `huϑ`, `huθE`), so the ported theorem
`LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq` gives a convergent
sequence of homomorphisms `GE → GK` on the overlap; through `topEquiv` they are sections `τ s n` of the internal
Hom. `evalId` shows the defining identity on every affine `W` inside the overlap (by restriction, using `hθEn`,
`hθFn`, `hun`). `solution`: `t n s = τ s n`; the convergence `t (n+1) − t n ∈ I^(n+1)` follows componentwise
(`pi_mem_smul_top`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.isLocallyNoetherian_of_isProper`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.pi_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.mem_pow_smul_top_iff_of_isScalarTower`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.evalTop`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.evalTop_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.evalTop_bijective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.topEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.topEquiv_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.topEquiv_symm_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.ext_of_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.mem_pow_smul_top_of_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.pow_smul_top_eq_bot`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.phiIter`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.phiIter_lam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.phiIter_θF`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.exists_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.Y2bSol.evalId`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq` (same contribution).
Other imports: `Mathlib`.
