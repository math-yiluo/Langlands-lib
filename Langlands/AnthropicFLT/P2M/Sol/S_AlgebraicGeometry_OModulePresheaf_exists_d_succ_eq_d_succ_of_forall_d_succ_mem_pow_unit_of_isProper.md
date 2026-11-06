# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- Each FLT command `p2m_reactivate "N₁ N₂ …"` (from `P2M.Util`; it re-activates the scoped declarations of the namespaces) is replaced by `open scoped N₁ N₂ …`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper`.

Proof (namespace `SolKS`): an Artin–Rees statement for Čech coboundaries of the structure sheaf, by the same Rees
algebra method as the ported theorem `exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper`.

- Setup and cochains (identical to that port): the Rees algebra `R = Rr I`, the base changes `P'`, `P₁`, the Rees
  module `F'` of `O_P` on `P'` (coherent, quasi-coherent), the pulled-back cover `K'`, the coefficient maps
  `coeffC` commuting with `d`, and the cochains `zC = b t^k` for `b` with values in `I^k` (declarations from
  `preimage_iInf` through `d_zC_eq_zero`, with the same names and roles).
- `Main`: `IC m` is the set of `(i+1)`-cochains with values in `I^m` (`mem_IC`, `IC_anti`, `smul_mem_IC`) and
  `Dg m = d (IC m)`. `Z1`, `B1` are the `F'`-cocycles in degree `i+2` and the coboundaries among them (`mem_Z1`,
  `mem_B1`), and `M = Z1 / B1` is finite over `R` by the ported theorem `cechFinite_of_isProper`, hence noetherian
  (`mkM`, `mkM_add`, `mkM_smul`, `mkM_zero`, `mkM_eq_mkM`). A coboundary `b = d w` with values in `I^k` gives the
  class `cls k b` of `zZ k b = b t^k`; `N m` is spanned by the classes with `k ≤ m` (`gens`, `N_mono`) and stabilizes
  at some `c₀`. `Good c₀ x` says that `x` has a representative whose `t^j`-coefficients lie in `Dg (j − c₀)`, and
  every element of `N c₀` is good (`good_of_mem`). `main`: if `d w` has values in `I^(n+c₀)`, its class lies in
  `N (n + c₀) = N c₀`, and comparing `t^(n+c₀)`-coefficients gives `w'` with values in `I^n` and `d w' = d w`.
  `mem_pow_smul_top_iff` translates `I^m • ⊤` on sections into membership in the extended ideal.

`solution` applies `main` and this translation.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.preimage_iInf`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.appLE_congr_hom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Rr`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Rr.val`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Rr.coeff_mem`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Rr.mk`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Rr.incl`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.sA`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.sX`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.P'`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.fst'`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.π'`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.P₁`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.g`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.snd₁`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.p₁`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.sX_sA`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.isPullback_P'`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.isPullback_P₁`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.alg`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.alg_res`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.T`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.θ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.θ_C`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.θ_X`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.appLE_top_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.ΓSpecIso_inv_C`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.θ_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.θ_res`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.θ_bijective`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.closure_eq_top`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.algR`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.algR₁`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.algR₁_eq_θ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.g_appLE_algR`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.algR_res`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.g_appLE_res`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.φg`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.φg_app`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'val`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'_exists`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mem_F'_iff`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'_res_val`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'_smul_val`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'_rsmul_val`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'_add_val`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'_zero_val`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'_ext`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.isCoherent_F'`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.res_eq_zero_iff_of_eq`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.isQuasicoherent_F'`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.K'`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.K'_inter`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.hW'`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.hW`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.e_s`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.e'_s`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.haff`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.ΦC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.ΦC_θ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.θ_ΦC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.ΦC_res`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.ΦC_algR₁`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_add`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_zero`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_sub`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'valHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'valHom_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_d`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_smul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Sθ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mem_range_of_mem_Sθ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.C_mem_Sθ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.map_mem_Sθ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.monomial_mem_Sθ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.zC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'val_zC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.coeffC_zC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.F'val_d_zC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.d_zC_eq_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.IC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mem_IC`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.IC_anti`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.smul_mem_IC`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Dg`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Z1`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.B1`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mem_Z1`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mem_B1`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.M`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS`)
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mkM`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mkM_add`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mkM_smul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mkM_zero`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mkM_eq_mkM`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.zZ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.cls`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.gens`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.N`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.N_mono`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.Good`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.good_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.main`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.SolKS.mem_pow_smul_top_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` (Library).
Other imports: `Mathlib`.
