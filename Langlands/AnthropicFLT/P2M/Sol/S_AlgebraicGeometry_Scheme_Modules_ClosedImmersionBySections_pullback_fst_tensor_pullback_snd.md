# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 1 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 5 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Port edit (FLT line 20): the command `p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections"` is removed. Port edit: FLT `p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections"` (with the empty namespace) re-exports, at the root namespace, the private alias declared just above. Standard `export` needs a namespace, and within this file the private alias is already accessible by its full name, so the command is removed.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd`. Statement. `AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_fst_tensor_pullback_snd` (Segre
embedding): if `L` on `X ⟶ Spec R` and `M` on `Y ⟶ Spec R` give closed immersions by sections, then
`pr₁^* L ⊗ pr₂^* M` on `X ×_R Y` gives a closed immersion by sections over `Spec R`.

Proof. Section `Frame`: frames on opens and their behaviour under scalars and restriction. Choose
presentations of `L` and `M` with closed immersions into `ℙᴺ`, `ℙᴹ`; the sections `σᵢ ⊗ τⱼ` (tensor products
of frames are frames, ported `Scheme.Modules.IsFrameOn.tensorSections_monoidalV2`) give a presentation of
`pr₁^* L ⊗ pr₂^* M` with `(N + 1)(M + 1)` sections (ported
`Scheme.Modules.exists_projPresentation_of_iSup_eq_top` and
`Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq`), on the affine pieces
`pr₁⁻¹ D₊(Xᵢ) ∩ pr₂⁻¹ D₊(Yⱼ)` (ported `isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top`).
The induced morphism to `ℙ^{(N+1)(M+1)-1}` is the Segre-type map; it is a closed immersion because on
each chart the ring map from the chart of projective space is surjective (generation of the chart rings
by the ratios, sections `Generation`, `ProjRatio`, `Two`, …).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.map_homOfLE_refl`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.smul_left_injective_of_isFrameOn`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.smul_left_surjective_of_isFrameOn`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.isUnit_of_smul_frame_eq_frame`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.isFrameOn_map`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.PP`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.DD`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.chart`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.iSup_DD`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.iSup_chart`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.exists_mem_chart`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.isFrameOn_σ`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.rfun`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.rfun_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.pmap_congr`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.pmap_pmap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.pmap_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.surjective_comp_eqToHom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.awayToSection_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.app_awayToSection_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.mem_closure_awayToSection`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.mem_DD_of_isUnit_germ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.mem_chart_of_isUnit_rfun`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.modMap_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.ringMap_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.restrict_smul_eq`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.KK`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.KK_succ`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.idx`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.ρ`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.WW`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.iSup_WW`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.exists_mem_WW`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.isFrameOn_ρ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.exists_segre`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.map_ρ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.chart_segre_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.rfun_segre_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.copyOver`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.isAffineOpen_DD`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.P2mSegreCI.closedImmersionBySections`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top` (same contribution).
Other imports: `Mathlib`.
