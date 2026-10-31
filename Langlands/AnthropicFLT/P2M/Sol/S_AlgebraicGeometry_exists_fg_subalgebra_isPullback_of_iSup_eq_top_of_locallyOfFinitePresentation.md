# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate` command(s) (an FLT command from `P2M.Util` that re-activates scoped extensions) are removed; the file compiles without them.
- The command `p2m_export "UnionModel" "ι"` (an FLT command from `P2M.Util` that adds an alias) is removed. Instead, the private abbreviation that FLT declares as `_root_.UnionModel.ι` is declared as `ι` inside the enclosing namespace `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel`, which is the name the alias provided; its definition and all uses are unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. A `UnionModel.Model B gY` packages a model over `Spec B` of a morphism `gY : Y ⟶ Spec A`; models
can be pushed to larger rings (`Model.map`, `toStage`) and restricted to opens (`restrictOpen`). Take
models of `U` over `T₁` and of `V` over `T₂ ⊇ T₁`, and push the model of `U` to `T₂`. Descend the
quasi-compact open `U ∩ V` to an open of the model of `U` and then of the model of `V`
(`Model.exists_open`, via the open-descent theorem), passing to larger stages `T₃ ⊆ T₄`; restrict the
two models to these opens to get two models of `U ∩ V`, and descend the comparison isomorphism between
them (`Model.exists_iso`, via the isomorphism-descent theorem) to a stage `T₅`. Each enlargement of the
stage stays finitely generated over `A₀` by `Subalgebra.fg_restrictScalars_and_le_of_fg`. Finally glue the
two models over `T₅` along the descended opens with the gluing theorem
`exists_isPullback_glue_of_isPullback_of_isOpenImmersion`; the inclusions `inc` and the squares `sq_inc`
supply its hypotheses.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private abbrev `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.ι`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.ι_comp`
- structure `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model`
- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.q`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.q_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.q_snd`
- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.map`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.map_X₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.map_f₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.map_π`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.map_π_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.map_π_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.map_π_preimage`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.isCompact_fst_preimage`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.range_subset`
- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.restrictOpen`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.restrictOpen_X₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.restrictOpen_f₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.restrictOpen_π_ι`
- abbrev `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.toStage`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.exists_open`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.exists_iso`
- def `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.inc`
- scoped unnamed instance `instance : IsOpenImmersion (M.inc W₀ hc k h gW hgW B' φ hφ)`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.inc_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.inc_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.inc_f₀`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.inc_opensRange`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.rmap_π_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.rmap_π_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.UnionModel.Model.sq_inc`
- theorem `P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion`, `Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_fg_restrictScalars_and_le_of_fg`.
All modules also import `Mathlib`.
