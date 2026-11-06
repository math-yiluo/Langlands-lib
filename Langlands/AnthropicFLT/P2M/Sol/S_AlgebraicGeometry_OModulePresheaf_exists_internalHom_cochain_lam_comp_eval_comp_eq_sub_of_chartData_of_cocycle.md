# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle`.

Proof (namespace `Y2bSol`). General helpers as in the neighbouring ports (`pi_mem_smul_top`,
`mem_pow_smul_top_iff_of_isScalarTower`, the identification `topEquiv` of internal-Hom sections over an affine with
module homomorphisms: `evalTop`, `evalTop_apply`, `evalTop_bijective`, `topEquiv_apply`, `topEquiv_symm_top`,
`ext_of_top`, `mem_pow_smul_top_of_top`). Čech helpers: `1`- and `2`-simplices given by increasing pairs and triples
(`Idx.pair`, `le_inter_pair`, `Idx.triple`, `eq_triple`, `face_triple_zero`, `face_triple_one`,
`face_triple_two`, `le_inter_triple`), the formula for `d` on `1`-cochains (`d_one_apply`) and pointwise operations
on internal-Hom sections (`add_val_apply`, `sub_val_apply`). Frame: `isLocallyNoetherian_of_isProper`, iterated
transition maps `phiIter` (`phiIter_lam`, `phiIter_θF`). Using the cocycle condition `hcocy` of `u`, the defining
identity makes `lam m ∘ (d (t m) σ)` vanish on every `2`-simplex `σ` (`lam_d_val_eq_zero`), and the Artin–Rees
bound `hlami` then gives `cσ` with `d (t (n + cσ)) σ ∈ I^(n+1)` (`exists_shift_d_mem`).

`solution`: take `t` from the ported theorem `exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData` and
shift it by `C = max_σ cσ`: `t' n = t (n + C)`. The defining identity at level `n` follows from that at level `n + C`
by applying `phiIter` (`phiIter_lam`, `phiIter_θF`); `d (t' n) ∈ I^(n+1)` componentwise; and the convergence of
`t'` follows from that of `t`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.pi_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.mem_pow_smul_top_iff_of_isScalarTower`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.evalTop`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.evalTop_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.evalTop_bijective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.topEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.topEquiv_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.topEquiv_symm_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.ext_of_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.mem_pow_smul_top_of_top`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.pair`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.le_inter_pair`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.triple`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.eq_triple`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.face_triple_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.face_triple_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.face_triple_two`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.Idx.le_inter_triple`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.d_one_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.add_val_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.sub_val_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.isLocallyNoetherian_of_isProper`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.phiIter`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.phiIter_lam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.phiIter_θF`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.lam_d_val_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.Y2bSol.exists_shift_d_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul` (same contribution).
Other imports: `Mathlib`.
