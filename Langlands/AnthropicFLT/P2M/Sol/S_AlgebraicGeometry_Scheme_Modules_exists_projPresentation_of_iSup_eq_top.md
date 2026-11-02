# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 22 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 11 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 1 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 18 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top`. Statement. `AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top`: let `σ₀, …, σ_N` be global sections
of a module `M` on `X ⟶ Spec R` and `U₀, …, U_N` opens covering `X` such that `σᵢ` is a frame of `M` on every
open inside `Uᵢ`. Then there is a `ProjPresentation` of `M` with these sections, whose morphism to `ℙᴺ_R`
maps each `Uᵢ` into the chart `D₊(Xᵢ)`.

Proof. Frames (`IsFrameOn`): coefficients `coef` with respect to a frame, their compatibility with
restriction and sums, the largest open `maxOpen` on which `σᵢ` is a frame. On `Uᵢ` the coordinates of the
`σⱼ` with respect to `σᵢ` (`trans i j`) are functions satisfying the cocycle identities
(`trans_mul_trans`, `trans_self`, `isUnit_trans` on overlaps); they define `R`-algebra maps `evalHom` from
the chart rings of `ℙᴺ_R` sending `Xⱼ/Xᵢ` to `trans i j`, hence morphisms `Uᵢ ⟶ D₊(Xᵢ)`. These agree on
overlaps and glue to `X ⟶ ℙᴺ_R` over `Spec R`; on the preimage of `D₊(Xᵢ)` (which contains `Uᵢ`, and is
`maxOpen σᵢ`) `σᵢ` is a frame and `(Xⱼ/Xᵢ) σᵢ = σⱼ`, so this is a presentation.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.resTop`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.resTop_map'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.resTop_map`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.resTop_top`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.mono`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.bijective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.injective`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.coef`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.coef_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.coef_eq_iff`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.coef_smul_resTop`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.coef_resTop`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.map_coef'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.map_coef`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.coef_add`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.coef_smul'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.of_eq_unit_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.isUnit_of_eq_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.of_forall_exists`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.maxOpen`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.le_maxOpen`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.maxOpen_isFrameOn`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.algR`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.map_comp_algR`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.map_algR`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.trans`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.trans_smul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.trans_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.map_trans`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.trans_mul_trans`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.trans_mul_trans_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.isUnit_trans`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.evalHom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.evalHom_X`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.evalHom_C`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.evalHom_X_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.isUnit_evalHom_X_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.map_comp_evalHom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom_mk`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom_ratio`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom_comp_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.map_comp_chartHom`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.map_chartHom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chart`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.homOfLE_chart`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chart_π`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.eval₂_mul_of_isHomogeneous`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.XX_mem_two`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.XX_eq_left`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.XX_eq_right`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.evalHom_eq_mul_evalHom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom₂`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom₂_mk_mul`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.isUnit_evalHom_XX_left`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.isUnit_evalHom_XX_right`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom₂_left_mk`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom₂_right_mk`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom₂_left_eq_right`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom₂_left_comp_awayMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chartHom₂_right_comp_awayMap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn.chart_eq_chart`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.Umax`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.isFrameOn_Umax`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.le_Umax`
- abbrev `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.chartMax`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.cover`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.charts_compatible`
- private def `AlgebraicGeometry.Scheme.Modules.LinSys.toProj`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.ι_toProj`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.homOfLE_ι_toProj`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.toProj_π`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.appLE_awayToSection_of_fac`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.Umax_le_preimage`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.chart_preimage_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.preimage_le_Umax`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.preimage_eq_Umax`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.isFrameOn_preimage`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.map_app_awayToSection_ratio`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.app_ratio_smul`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.projPresentation`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Scheme.Modules.exists_projPresentation_of_iSup_eq_top'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution).
Other imports: `Mathlib`.
