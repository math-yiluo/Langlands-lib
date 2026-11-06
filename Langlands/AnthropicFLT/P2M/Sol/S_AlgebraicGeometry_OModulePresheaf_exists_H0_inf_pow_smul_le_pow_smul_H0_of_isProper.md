# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper`;
it is `FF0SepSqZeroAux.main`.

Proof: reduction to the structure sheaf (namespace `FF0SepSqZeroAux`). As in the port of
`exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper`, the trivial square-zero extensions
`T U = Γ(P, U) ⊕ F(U)` glue (for `F` quasi-coherent) to a scheme `Y hq` with a morphism `p hq : Y ⟶ P` that
is finite for `F` coherent (`isFinite_p`), so `p hq ≫ q` is proper; the sections of `Y` over the pulled-back
cover `KY` are the rings `T` (`eY`, `Φ`, `Ψ`), and the Čech differential of the structure sheaf of `Y`
restricts on the `F`-components to the differential of `F` (`Φ_d`, `snd_dT`, `dT_inr`). Section `Transport`:
the `A`-linear maps `L : C⁰(F) → C⁰(𝒪_Y)`, `z ↦ inr ∘ z`, and `Q`, taking `F`-components, satisfy
`Q ∘ L = id` and preserve `H⁰` (`Q_L`, `L_mem_H0`, `Q_mem_H0`; `eY_smul` and `σT_mul_inr` for linearity).

`main`: apply the ported unit case `exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper` to
`p hq ≫ q` and `KY`; for `z ∈ H⁰(F) ∩ I^(n+c) • C⁰`, `L z` lies in the corresponding intersection for `𝒪_Y`,
hence in `I^n • H⁰(𝒪_Y)`, and applying `Q` gives `z = Q (L z) ∈ I^n • H⁰(F)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.instModuleMop`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.instIsCentralScalar`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.T`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.rmap`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.fst_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.snd_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ρ_inl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ρ_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ρ_refl`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ρ_comp`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ρ_ρ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Tfun`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Tfun_obj`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Tfun_map`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.α`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.α_app`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.coequifibered`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.D`
- instance (anonymous, in namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux`)
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Y`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ιU`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.D_cover_f`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ιU_isOpenImmersion`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.D_functor_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.isOpenImmersion_SpecMap_ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.SpecMap_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ι_toBase`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.toBase_preimage`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.opensRange_functor_map_basicOpen`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.SpecMap_ρ_ι`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.appLE_congr_hom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.appLE_top_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.preimage_ι_eq_top`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.le_preimage_ι`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.eHom`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.isIso_eHom`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.e`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.e_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.map_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.e_map`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.appLE_eHom`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.e_appLE`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.isFinite_p`
- instance `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.isAffineHom_p`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.σT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.σT_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.algebraMap_smul_eq`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Ks`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.KY`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.toP`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Ymap_Ymap`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Ymap_id`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.toP_ofP`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.ofP_toP`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.eY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.eY_apply`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.σY`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.eY_σY`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Φ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Ψ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Φ_Ψ`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.snd_dT`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.fst_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.snd_dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.dT_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Φ_d`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.σT_mul_inr`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.snd_σT_mul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.unitY_smul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.eY_smul`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.eY_symm_σT_mul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.L`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.L_apply`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Q`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Q_apply`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Q_L`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.L_mem_H0`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.Q_mem_H0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.FF0SepSqZeroAux.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_unit_of_isProper` (same contribution).
Other imports: `Mathlib`.
