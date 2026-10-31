# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- Mathlib-drift repair in the proof of `sheafify_μ_app_tensorSections` (statement unchanged):
  at FLT line 88 the call `ModuleCat.MonoidalCategory.tensorHom_tmul ...` now names its ring explicitly,
  `(R := Γ(X, U))`. In the pinned Mathlib this lemma needs a `CommRing` instance on the ring,
  and instance search did not find one on the definitionally equal ring
  `(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)` that elaboration inferred.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 12: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry N.AlgebraicGeometry"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 20: `p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.sheafify Scheme.Modules.tensorSections"` becomes `export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.sheafify Scheme.Modules.tensorSections)`.
  - FLT line 22: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 7 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names.
  - FLT line 24: `p2m_export "AlgebraicGeometry.Scheme.Modules" "tensor sheafify tensorIsoSheafify tensorSections"` becomes `export _root_.AlgebraicGeometry.Scheme.Modules (tensor sheafify tensorIsoSheafify tensorSections)`.
  - FLT line 25: `p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry`.
  - FLT line 29: `p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TensorProduct"` becomes `open CategoryTheory CategoryTheory.MonoidalCategory Opposite TensorProduct`.
- No other change: the declarations, statements and the rest of the proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- abbrev `adj`
- abbrev `ι`
- def `sheafifyTensorIso`
- lemma `tensorSections_eq`
- lemma `sheafify_map_val_app_unit`
- lemma `map_tensorHom_unit_comp`
- theorem `sheafify_μ_app_tensorSections`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom`, `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`, `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`.
