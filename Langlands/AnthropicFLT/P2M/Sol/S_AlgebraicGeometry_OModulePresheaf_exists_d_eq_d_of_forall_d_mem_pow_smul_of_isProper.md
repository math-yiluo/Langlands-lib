# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper`.

Proof (namespace `FormalGAGAFiniteSqZeroAux`): reduction from a coherent module `F` to the structure sheaf of the
trivial square-zero extension `O_P ⊕ F`. On each affine `U`, `T F U` is the ring `TrivSqZeroExt Γ(P, U) F(U)`, with
restriction ring maps `ρ` (`ρ_comp`, `ρ_refl`); these form a functor `Tfun` on the affine Zariski site with a
natural map `α` from the structure sheaf, which is coequifibered when `F` is quasi-coherent (`coequifibered`).
Section `Scheme`: Mathlib's relative gluing (`relativeGluingData`) of the spectra `Spec (T F U)` gives a scheme `Y`
with an affine morphism `p : Y ⟶ P` whose preimage of `U` is `Spec (T F U)` (`toBase_preimage`); section
`Sections`: `Γ(Y, p⁻¹ U) ≃ T F U` (`e`), compatibly with restriction and with `p` (`e_map`, `e_appLE`), and `p` is
finite when `F` is coherent (`isFinite_p`), so `p ≫ q` is proper. Section `Ideals`: the extension of `I'` to
`T F U` has second components in `I' • F(U)`, and contains `inr m` for `m ∈ I' • F(U)` (`snd_mem_of_mem_map_σT`,
`inr_mem_map_σT`). Section `Cech`: the pullback cover `KY` of `K`, and the identification `Φ`/`Ψ` of Čech cochains
of the structure sheaf of `Y` with families in the `T F (K.inter s)`, under which the differential becomes
componentwise (`Φ_d`, `snd_dT`, `dT_inr`).

`main`: the Library theorem `OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper` for the proper
morphism `p ≫ q` and the cover `KY` gives `c`. For a cochain `w` of `F` with differential in `I^(n+c) • ⊤`, the
cochain `inr ∘ w` of `O_Y` has differential in `I^(n+c) O_Y`, so there is `w'Y` with components in `I^n O_Y` and the
same differential; the second components of `Φ w'Y` form the required cochain `w'` of `F`. `solution` is
`FormalGAGAFiniteSqZeroAux.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.instModuleMop`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.instIsCentralScalar`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.T`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.rmap`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.fst_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.snd_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_inl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_refl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_comp`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_ρ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Tfun`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Tfun_obj`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Tfun_map`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.α`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.α_app`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.coequifibered`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.D`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux`)
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Y`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ιU`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.D_cover_f`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ιU_isOpenImmersion`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.D_functor_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.isOpenImmersion_SpecMap_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.SpecMap_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ι_toBase`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.toBase_preimage`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.opensRange_functor_map_basicOpen`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.SpecMap_ρ_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.appLE_congr_hom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.appLE_top_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.preimage_ι_eq_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.le_preimage_ι`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.eHom`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.isIso_eHom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.e`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.e_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.map_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.e_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.appLE_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.e_appLE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.isFinite_p`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.isAffineHom_p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.σT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.σT_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.algebraMap_smul_eq`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.sections_smul_mem`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.smul_mem_of_fst_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.J`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.map_σT_le`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.snd_mem_of_mem_map_σT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.inr_mem_map_σT`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Ks`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.KY`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.toP`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Ymap_Ymap`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Ymap_id`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.toP_ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.ofP_toP`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.eY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.eY_apply`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.σY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.eY_σY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.eY_comp_σY`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Φ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Ψ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Φ_Ψ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.snd_dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.fst_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.snd_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.Φ_d`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.mem_map_σY_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.FormalGAGAFiniteSqZeroAux.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_smul_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper` (Library).
Other imports: `Mathlib`.
