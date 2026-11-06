# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- `p2m_export` also exports from namespaces that contain only private declarations of this module (`P2Sol`), which Lean does not register as namespaces; Lean's `export` rejects them, so each of them is registered by an empty block `namespace N end N` right after the options.
- Each FLT command `p2m_reactivate "N₁ N₂ …"` (from `P2M.Util`; it re-activates the scoped declarations of the namespaces) is replaced by `open scoped N₁ N₂ …`.
- Compatibility edit for the project's Mathlib: in the proof of `smul_eq_zero_chart`, the constant `DistribMulAction.toAddMonoidHom` (and its simp lemma `DistribMulAction.toAddMonoidHom_apply`) is replaced by `DistribSMul.toAddMonoidHom` (`DistribSMul.toAddMonoidHom_apply`). The old name does not exist in this Mathlib; both denote scalar multiplication by `j` as an additive monoid homomorphism, so the proof is otherwise unchanged.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct`.

Proof (namespace `P2Sol`): functoriality of the pullback.

- Separation for quasi-coherent presheaves: a section over an affine `V` vanishing on the basic opens of a
  generating set vanishes (`sep`, `sep_eq`).
- Charts: on a chart `V ⊆ p⁻¹ U`, `θ U V h = β₂ ∘ (id ⊗ ψ) ∘ β₁⁻¹ : G'₁(V) → G'₂(V)` is the base change of
  `ψ.app U` (`ψlin`, `ψlin_apply`, `chart_ext`, `θ`), with `θ (η₁ x) = η₂ (ψ x)` (`θ_eta`), compatible with
  restriction in `V` (`res_θ`) and independent of `U` (`θ_eq_of_le`, then `θ_eq` via a common refinement by basic
  opens: `span_eq_top_of_cover`, `bo`).
- Gluing: restrictions between basic opens of `V` are localizations (`rf`, `rf_rf`, `resV`, `resV_apply`,
  `basicOpen_mul_le_left`, `basicOpen_mul_le_right`, `isLocalizedModule_resV`), so the chart maps on a finite basic
  cover of an affine `V` (`exists_cover`) glue uniquely (`exists_glue`, using quasi-coherence of `G'₂`), giving
  `app V : G'₁(V) → G'₂(V)` agreeing with `θ` on every chart below `V` (`exists_app`, `app_spec`; sections are
  determined by their chart restrictions, `eq_of_forall_chart`). It is additive and `A`- and `Γ(V', V)`-linear
  (`θ_smulA`, `app_add`, `app_smulA`, `app_smul`, `appLin`, `appLin_apply`) and commutes with restriction
  (`res_app`), so it defines `ψ' : AffHom G'₁ G'₂` with `ψ' ∘ η₁ = η₂ ∘ ψ` (`app_eta`, `app_eq_θ`).
- Exactness: `θ` is surjective when `ψ.app U` is (right exactness of the tensor product, `θ_surjective`), and
  gluing (with quasi-coherence of `G'₁` to clear denominators, `exists_num`) gives surjectivity of `ψ'`
  (`app_surjective`). If `ker (ψ.app U) = J • ⊤`, then `J` kills `G'₂` (`smul_eq_zero_chart`, `smul_eq_zero`), the
  kernel of each `θ` lies in `J • G'₁` (`JΓ`, `mem_JΓ`, `θ_ker_le`), and gluing gives
  `ker (ψ'.app V) = J • ⊤` (`app_ker`).

`solution` returns `ψ'` with `app_eta`, `app_surjective` and `app_ker`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.sep`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.sep_eq`
- def `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.ψlin`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.ψlin_apply`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.chart_ext`
- def `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.θ`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.θ_eta`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.res_θ`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.θ_eq_of_le`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.span_eq_top_of_cover`
- abbrev `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.bo`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.θ_eq`
- abbrev `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.rf`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.rf_rf`
- def `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.resV`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.resV_apply`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.basicOpen_mul_le_left`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.basicOpen_mul_le_right`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.isLocalizedModule_resV`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.exists_glue`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.exists_cover`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.exists_app`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.θ_smulA`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.eq_of_forall_chart`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.θ_surjective`
- def `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.JΓ`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.mem_JΓ`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.smul_eq_zero_chart`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.θ_ker_le`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.exists_num`
- private def `P2Sol.app`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.app_spec`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.app_add`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.app_smulA`
- private theorem `P2Sol.app_smul`
- def `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.appLin`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.appLin_apply`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.res_app`
- def `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.ψ'`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.app_eta`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.app_eq_θ`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.app_surjective`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.smul_eq_zero`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.P2Sol.app_ker`
- theorem `P2Sol.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent` (Library), `Langlands.AnthropicFLT.Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top` (same contribution).
Other imports: `Mathlib`.
