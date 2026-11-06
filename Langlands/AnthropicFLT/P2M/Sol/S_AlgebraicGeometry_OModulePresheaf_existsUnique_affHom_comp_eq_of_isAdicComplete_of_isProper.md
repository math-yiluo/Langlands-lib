# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`
(full faithfulness of completion for coherent sheaves on a proper scheme over a complete noetherian ring).

Proof (namespace `HomCompleteAux`). Section `Generic`: elementary facts on `J • ⊤` (under linear maps, linear
equivalences, finite products and submodules), extensionality for `AffHom`, the degree-`0` Čech differential, and
`coverOfCompact` (a finite ordered affine cover of a quasi-compact scheme). Structure `Sys` bundles the data `F`,
`G`, `Gn`, `τ`, `ρ`, `ψ` and the hypotheses; `K` is a finite ordered affine cover of `X`, `IU U` the extension of `I`
to `Γ(X, U)`, and `H := internalHom F G` is coherent and quasi-coherent (ported theorem
`isCoherent_internalHom_and_existsUnique_eval_eq`; `X` is locally noetherian).

Local step (section `Local`, on an affine `U`): `H(U) ≅ Hom_{Γ(X,U)}(F(U), G(U))` (`evalE`, by the same ported
theorem and `internalHom_ext_of_apply_self_eq`); `Gn n (U) ≅ G(U) / I^(n+1) G(U)` (`eQ`); the `ψ n` give compatible
maps `psiT n : F(U) → G(U) / I^(n+1)`, and the ported theorem
`Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq` gives a unique compatible family `Phi`
in the truncations of `Hom(F(U), G(U))` lifting them (`hal`). Representatives `rep U n ∈ H(U)` are congruent
modulo `I^(n+1)` in `n` and induce `ψ n` after `ρ n` (`rep_alpha`, `rep_succ_sub_rep`), and any other such
sequence agrees with `rep` modulo `I^(n+1)` (`sub_rep_mem_of_classes`); restrictions of representatives are
representatives (`res_rep_sub_rep_mem`, `res_rep_sub_res_rep_mem`).

Globalisation: the cochains `hcoch n = (rep (K.inter s) n)_s` have differential in `I^(n+1) • ⊤`
(`d_hcoch_mem`), so the ported theorem `exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper` corrects them to
cocycles `zc m` congruent to `hcoch m` modulo `I^(m+1)` (`exists_cocycle`). With the Artin–Rees constants `cAR`
from the ported theorem `exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper`, the subsequence `gseq k = zc (Nm k)`
is Cauchy in `H0` (`zc_sub_zc_mem`, `gseq_cauchy`). `H0` is a finite module (Library theorem `cechFinite_of_isProper`)
over the complete ring `R`, hence `I`-adically complete (ported theorem `IsAdicComplete.of_finite_of_isNoetherianRing`),
so the sequence has a limit `L` (`exists_limit`), a cocycle congruent to the representatives at every level
(`L_sub_rep_mem`). The ported theorem `internalHom_d_zero_eq_zero_iff_existsUnique` glues `L` to a global section
`Lt` of `H` (`exists_glued`), and `phi := internalHom.toAffHom Lt` satisfies `ρ n ∘ phi = ψ n` (`Lt_alpha`,
`phi_spec`). Uniqueness (`phi_unique`): for another solution `φ'`, the restrictions of the difference of global
sections form a cocycle with components in `I^k • ⊤` for all `k`, which vanishes by the ported theorem
`eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper`; gluing uniqueness gives `φ' = phi`. `main` packages
this, and `solution` applies it to the bundled data.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.map_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.mem_smul_top_iff_of_linearEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.pi_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.apply_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.mem_smul_top_of_coe_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.coe_mem_of_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.affHom_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.d_zero_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.d_zero_res_eq_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.coverOfCompact`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.A`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.isLN`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.noeth`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.compactSpace`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.K`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.IU`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.H`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.H_coh_qc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.hρc_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.hψ_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.smul_Gn_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.sections_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.isQuasicoherent_Gn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.mem_IU_pow_smul_top_iff`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.HomU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.res_refl_fun`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.evalA`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.evalA_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.evalA_bijective`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.evalE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.evalE_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.sub_mem_iff_evalE`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.PU`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.PU_eq_ker`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.eQ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.eQ_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.eQ_symm_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.psiT`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.psiT_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.PU_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.factor_psiT`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.mkQ_comp_eq_psiT_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.hal`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Phi_compat`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Phi_alpha`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Phi_unique`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.classes_eq_Phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.alpha_of_class`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.evalE_rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.mk_evalE_rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.rep_alpha`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.rep_succ_sub_rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.rep_sub_rep_of_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.sub_rep_mem_of_classes`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.alpha_of_sub_rep_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.pushFam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.pushFam_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.psiFam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.psiFam_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.alpha_below`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.res_rep_sub_rep_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.res_rep_sub_res_rep_mem`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Us`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.hcoch`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.d_hcoch_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.exists_cocycle`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.zc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.d_zc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.zc_sub_rep`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.zc_mem_H0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.zc_succ_sub_zc_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.cAR`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.cAR_spec`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Nm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.le_Nm`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Nm_mono`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.zc_sub_zc_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.gseq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.gseq_cauchy`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.finite_H0`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.isAdicComplete_H0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.exists_limit`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.L`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.gseq_sub_L`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.L_sub_rep_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.d_L`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.exists_glued`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Lt`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.res_Lt`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Lt_unique`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.Lt_alpha`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.phi_spec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.phi_unique`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.HomCompleteAux.Sys.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library), `Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing` (same contribution).
Other imports: `Mathlib`.
