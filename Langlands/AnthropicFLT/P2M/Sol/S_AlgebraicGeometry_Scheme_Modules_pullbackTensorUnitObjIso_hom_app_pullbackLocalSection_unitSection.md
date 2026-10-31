# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 20: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry N.AlgebraicGeometry Opposite TensorProduct"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite TensorProduct`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 21: `p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"` becomes `open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal`.
  - FLT line 26: `p2m_export "AlgebraicGeometry" "…"` with 10 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 28: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 22 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names.
  - FLT line 30: `p2m_export "AlgebraicGeometry.Scheme.Modules" "…"` with 18 names becomes `export _root_.AlgebraicGeometry.Scheme.Modules (…)` with the same names.
  - FLT line 31: `p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry`.
  - FLT line 38: `p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackTensorSections" "adj"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections (adj)`.
  - FLT line 44: `p2m_export "AlgebraicGeometry.Scheme.Modules.PullbackTensorSections" "pf"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections (pf)`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- abbrev `_root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.adj`
- abbrev `ι`
- abbrev `_root_.AlgebraicGeometry.Scheme.Modules.PullbackTensorSections.pf`
- abbrev `adj₀`
- abbrev `e`
- def `pb₀Section`
- def `shUnit`
- lemma `sheafify_map_app_shUnit`
- lemma `counit_app_shUnit`
- lemma `homEquiv_symm_app_pb₀Section`
- lemma `e_hom_app_pullbackLocalSection`
- lemma `e_inv_app_shUnit`
- lemma `pb₀_δ_eq`
- lemma `pb₀_δ_app_pb₀Section_tmul`
- lemma `sheafify_δ_app_shUnit_tmul`
- lemma `e_hom_app_tensor_comp_δ`
- lemma `pf_ε_app`
- lemma `pb₀_η_app_pb₀Section`
- lemma `pb₀_ε_app`
- lemma `sheafify_ε_app`
- lemma `pullback_ε_app_unitSection`
- theorem `pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection`
- theorem `pullbackTensorUnitObjIso_hom_app_pullbackLocalSection'`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom`, `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`, `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal`, `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_PullbackMonoidal`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections`.
