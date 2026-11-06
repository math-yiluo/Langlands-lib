# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper`.

Proof: reduction to the structure sheaf of a square-zero extension (namespace
`FormalGAGAFiniteSqZeroAux`). For each affine open `U`, `T U` is the trivial square-zero extension
`Γ(P, U) ⊕ F(U)` (`TrivSqZeroExt`), with restriction maps `ρ`; this gives a functor `Tfun` on the affine
Zariski site with a natural map `α` from `𝒪_P`, which is coequifibered when `F` is quasi-coherent
(`coequifibered`). Gluing the spectra gives a scheme `Y hq` with `p hq : Y ⟶ P` (relative spectrum,
`D`, `ιU`, `ι_toBase`, `toBase_preimage`), and the sections of `Y` over `p⁻¹ U` are identified with
`T U` (`eHom`, `e`, `e_map`, `e_appLE`). For `F` coherent, `p hq` is finite (`isFinite_p`, from the ported
`isFinite_toBase_relativeGluingData`), so `p hq ≫ q` is proper.

The section `Ideals` compares `I'`-multiples: `σT : A → T U`, the ideal `J`, and `inr_mem_map_σT`,
`snd_mem_of_mem_map_σT` (the `F`-component of an element of `I' T U` lies in `I' • F(U)` and conversely for
elements `inr m`). The section `Cech` pulls the cover `K` back to `Y` (`KY`), identifies Čech cochains of
the structure sheaf of `Y` on `KY` with families in `T` (`eY`, `Φ`, `Ψ`, `Φ_Ψ`), and shows that the Čech
differential becomes `dT`, whose `F`-component is the differential of `F` (`Φ_d`, `snd_dT`, `dT_inr`).

`main`: apply the Library theorem `OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper` (the
statement for the structure sheaf of a proper scheme) to `p hq ≫ q` and the cochain `inr ∘ w`, and take the
`F`-components of the cochain it produces. `solution` converts between the componentwise conditions of
`main` and membership in `I^k • ⊤` of the product modules (namespace `FormalGAGAFiniteSqZeroDock`:
`apply_mem_smul_top`, `single_mem_smul_top`, `mem_smul_top_of_forall`) and takes `a := t - w'`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.instModuleMop`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.instIsCentralScalar`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.T`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.rmap`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.fst_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.snd_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_inl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_refl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_comp`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ρ_ρ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Tfun`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Tfun_obj`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Tfun_map`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.α`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.α_app`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.coequifibered`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.D`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux`)
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Y`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ιU`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.D_cover_f`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ιU_isOpenImmersion`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.D_functor_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.isOpenImmersion_SpecMap_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.SpecMap_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ι_toBase`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.toBase_preimage`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.opensRange_functor_map_basicOpen`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.SpecMap_ρ_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.appLE_congr_hom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.appLE_top_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.preimage_ι_eq_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.le_preimage_ι`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.eHom`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.isIso_eHom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.e`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.e_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.map_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.e_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.appLE_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.e_appLE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.isFinite_p`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.isAffineHom_p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.σT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.σT_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.algebraMap_smul_eq`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.sections_smul_mem`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.smul_mem_of_fst_mem`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.J`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.map_σT_le`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.snd_mem_of_mem_map_σT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.inr_mem_map_σT`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Ks`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.KY`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.toP`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Ymap_Ymap`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Ymap_id`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.toP_ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.ofP_toP`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.eY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.eY_apply`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.σY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.eY_σY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.eY_comp_σY`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Φ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Ψ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Φ_Ψ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.snd_dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.fst_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.snd_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.Φ_d`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.mem_map_σY_iff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroAux.main`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroDock.apply_mem_smul_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroDock.single_mem_smul_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.FormalGAGAFiniteSqZeroDock.mem_smul_top_of_forall`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper` (Library).
Other imports: `Mathlib`.
