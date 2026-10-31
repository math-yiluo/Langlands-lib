# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit`

Ported for task `8836e68b-90ba-4f01-a129-026ad9adfa9d` (descent of smoothness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `AlgEquivSpreadDirected`). Descend `e` and `e.symm` to algebra maps `φ₀`, `ψ₀` over two
stages with the algebra-map theorem
(`Algebra.exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit`) and move both to a
common stage `j₀` (`relevel`, `square_relevel`). The composites `ψ₁ ∘ φ₁` and `φ₁ ∘ ψ₁` agree with the
identities after base change to `R`, so by the finite-type theorem
(`Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit`) they agree with the identities
at later stages. At a common later stage `j` the relevelled maps are mutually inverse (checked on the
elements `1 ⊗ a` with `Algebra.TensorProduct.ext`), and `e₀ = AlgEquiv.ofAlgHom φ₂ ψ₂`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.toR`
- abbrev `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.mapT`
- abbrev `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.stepT`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.mapT_stepT`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.stepT_stepT`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.tmul_one_eq_algebraMap`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.tmul_one_eq_algebraMap_R`
- def `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.relevel`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.relevel_tmul`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.stage_tmul_one`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.relevel_stepT`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.square_relevel`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgEquivSpreadDirected.exists_algEquiv`
- theorem `P2MW.S_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit` (same contribution).
All modules also import `Mathlib`.
