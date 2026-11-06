# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper`.

Proof (namespace `ThickeningTransportAux`): the Čech complex of a coherent `F` is a retract of the Čech complex of
the structure sheaf of the square-zero thickening `Y = Spec_P(O_P ⊕ F)`.

- The rings `T F U = Γ(P, U) ⊕ F(U)` (Mathlib `TrivSqZeroExt`; `instModuleMop`, `instIsCentralScalar`) with
  restriction ring maps `ρ` (`rmap`, `fst_ρ`, `snd_ρ`, `ρ_inl`, `ρ_inr`, `ρ_refl`, `ρ_comp`, `ρ_ρ`) form a functor
  `Tfun` on the affine Zariski site of `P` (`Tfun_obj`, `Tfun_map`) with a map `α` from the structure sheaf
  (`α_app`), which is coequifibered when `F` is quasi-coherent (`coequifibered`).
- Mathlib's relative gluing along the directed affine cover gives the scheme `Y` with `p : Y ⟶ P` (`D`, `Y`, `p`,
  charts `ιU`, `D_cover_f`, `ιU_isOpenImmersion`, `D_functor_map`, `isOpenImmersion_SpecMap_ρ`, `SpecMap_ι`,
  `ι_toBase`, `toBase_preimage`, `opensRange_functor_map_basicOpen`, `SpecMap_ρ_ι`). Over each affine `U`,
  `Γ(Y, p⁻¹ U) ≅ T F U` (`appLE_congr_hom`, `appLE_top_top`, `preimage_ι_eq_top`, `le_preimage_ι`, `eHom`,
  `isIso_eHom`, `e`, `e_apply`, `map_eHom`, `e_map`, `appLE_eHom`, `e_appLE`). `p` is finite for coherent `F`
  (`isFinite_p`, from the ported theorem `Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData`) and affine
  (`isAffineHom_p`). The `A`-structure: `σT`, `σT_apply`, `algebraMap_smul_eq`.
- Čech comparison (`q` separated): the pulled-back cover `KY = K.comap p` (`Ks`, `KY`) has sections
  `Γ(Y, KY.inter s) ≅ T F (K.inter s)` (`toP`, `ofP`, `Ymap_Ymap`, `Ymap_id`, `toP_ofP`, `ofP_toP`, `eY`,
  `eY_apply`, `σY`, `eY_σY`), so cochains of the unit presheaf on `KY` are families in `T F` (`Φ`, `Ψ`, `Φ_Ψ`,
  `Ψ_Φ`) with differential `dT` acting on the `F`-component as the Čech differential of `F` (`snd_dT`, `fst_dT_inr`,
  `snd_dT_inr`, `dT_inr`, `Φ_d`).
- Transport: `L z = Ψ (inr ∘ z)` and `Q v = (Φ v).snd` are `A`-linear (`σT_mul_inr`, `snd_σT_mul`, `unitY_smul`,
  `eY_smul`, `eY_symm_σT_mul`, `L_apply`, `Q_apply`), with `Q ∘ L = id` and both commuting with the differentials
  (`Q_L`, `d_L`, `d_Q`).

`solution`: `Y` with `p ≫ q` (proper, since `p` is finite), the cover `KY`, and `L`, `Q`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.instModuleMop`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.instIsCentralScalar`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.T`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.rmap`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.fst_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.snd_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ρ_inl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ρ_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ρ_refl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ρ_comp`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ρ_ρ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Tfun`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Tfun_obj`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Tfun_map`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.α`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.α_app`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.coequifibered`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.D`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux`)
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Y`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ιU`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.D_cover_f`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ιU_isOpenImmersion`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.D_functor_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.isOpenImmersion_SpecMap_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.SpecMap_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ι_toBase`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.toBase_preimage`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.opensRange_functor_map_basicOpen`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.SpecMap_ρ_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.appLE_congr_hom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.appLE_top_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.preimage_ι_eq_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.le_preimage_ι`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.eHom`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.isIso_eHom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.e`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.e_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.map_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.e_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.appLE_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.e_appLE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.isFinite_p`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.isAffineHom_p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.σT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.σT_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.algebraMap_smul_eq`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Ks`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.KY`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.toP`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Ymap_Ymap`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Ymap_id`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.toP_ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.ofP_toP`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.eY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.eY_apply`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.σY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.eY_σY`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Φ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Ψ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Φ_Ψ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Ψ_Φ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.snd_dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.fst_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.snd_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Φ_d`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.σT_mul_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.snd_σT_mul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.unitY_smul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.eY_smul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.eY_symm_σT_mul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.L`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.L_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Q`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Q_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.Q_L`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.d_L`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.ThickeningTransportAux.d_Q`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData` (same contribution).
Other imports: `Mathlib`.
