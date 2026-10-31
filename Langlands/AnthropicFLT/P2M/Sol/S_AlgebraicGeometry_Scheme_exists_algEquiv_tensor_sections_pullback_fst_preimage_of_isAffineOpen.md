# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 10: `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry N.AlgebraicGeometry TensorProduct"` becomes `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 17: `p2m_export "AlgebraicGeometry" "…"` with 32 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 19: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 20 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names.
  - FLT line 21: `p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom pullback"` becomes `export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (specMap algebraOfHom algebraMap_algebraOfHom pullback)`.
  - FLT line 22: `p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry`.
  - FLT line 32: `p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "fst"` becomes `export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange (fst)`.
  - FLT line 36: `p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "snd"` becomes `export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange (snd)`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- abbrev `XA`
- abbrev `_root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.fst`
- abbrev `_root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.snd`
- theorem `specMap_algebraMap_eq`
- def `pullbackAffineOpenIsoSpecTensor`
- def `sigma`
- theorem `sigma_apply`
- theorem `iso_hom_comp_sndLeg`
- theorem `iso_hom_comp_fstLeg`
- theorem `opens_ι_appTop_topIso_hom`
- theorem `topIso_morphismRestrict_appTop_topIso`
- theorem `sigma_tmul_one`
- theorem `sigma_one_tmul`
- theorem `algebraMap_sndAlgebra`
- def `algEquiv`
- theorem `algEquiv_one_tmul`
- theorem `exists_algEquiv_sections_baseChange`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`.
