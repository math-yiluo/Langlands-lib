# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete`.

Proof (namespace `P2mProjExistSol`): Grothendieck existence for closed subschemes of `ℙ^r_A`, by presenting the
adic system as a cokernel. Helpers: generic lemmas on `J • ⊤` (`map_mem_smul_top`, `map_smul_top_of_surjective`,
`pow_smul_top_eq_bot`), extensionality of affine homomorphisms (`affHom_ext`), and the truncations
`trunc I E k = E / I^(k+1) E` with projections `truncπ` and transition maps `truncτ` (`T`, `T_def`, `T_smul_mem`,
`T_res`, `T_anti`, `truncModuleSections`, `trunc_obj`, `trunc_res_mk`, `trunc_smul_mk`, `truncπ_app`,
`truncπ_surjective`, `ker_truncπ`, `truncτ_app_mk`, `truncτ_truncπ`, `truncτ_comp_truncπ`, `truncτ_surjective`,
`ker_truncτ`, `isCoherent_trunc`, `isQuasicoherent_trunc`).

`main` (with `q = ι ≫ π`, which is proper):

1. The ported theorem `exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion`
   gives a coherent `E` with compatible surjections `θ k : E → F k`; they factor through `trunc I E k` as `θb k`
   (since `I^(k+1)` kills `F k`), compatibly with `truncτ`.
2. The ported theorem `exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top` gives an adic system `K` with maps
   `j k : K k → trunc I E k` onto `ker θb k`; step 1 applied to `K` gives a coherent `H` with compatible surjections
   `lam k : H → K k`.
3. The maps `j k ∘ lam k : H → trunc I E k` are compatible, so the ported theorem
   `existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper` (full faithfulness of completion, using that `A` is
   `I`-adically complete) lifts them to `h : H → E`. Then `ker θ k = range h + I^(k+1) E` on every affine.
4. The ported theorem `exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup` shows that
   `G = coker h` with the induced maps `ψ k` is the required coherent sheaf.

`solution` substitutes `q = ι ≫ π` and applies `P2mProjExistSol.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.map_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.map_smul_top_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.pow_smul_top_eq_bot`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.affHom_ext`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.T`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.T_def`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.T_smul_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.T_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.T_anti`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncModuleSections`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.trunc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.trunc_obj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.trunc_res_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.trunc_smul_mk`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncπ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncπ_app`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncπ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.ker_truncπ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncτ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncτ_app_mk`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncτ_truncπ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncτ_comp_truncπ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.truncτ_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.ker_truncτ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.isCoherent_trunc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.isQuasicoherent_trunc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.P2mProjExistSol.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup` (same contribution).
Other imports: `Mathlib`.
