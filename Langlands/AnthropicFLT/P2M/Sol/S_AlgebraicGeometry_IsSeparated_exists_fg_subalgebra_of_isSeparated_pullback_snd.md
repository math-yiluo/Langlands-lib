# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd`

Ported module of the proof submitted by task `8b63dc1d-84d3-43fa-a1d5-9657a89c8df1` (descent of separatedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `SepDescAux`). Take a finite affine open cover `Uᵢ → X` (`X` is quasi-compact). For a
morphism `g : Y ⟶ Spec A₀` from an affine `Y`, the base change `X_Y → Y` is separated iff for all `i, j`
the base change to `Y` of the chart map `Uᵢ ×_X Uⱼ → Uᵢ ×_{A₀} Uⱼ` (`chart`, `chartBC`) is a closed
immersion (`isSeparated_snd_iff`: the diagonal is checked on the cover by Mathlib's
`AffineTargetMorphismProperty.diagonal_of_openCover_source`, with the comparison isomorphisms `eS`, `eT` and
`isClosedImmersion_iff`). Each chart map is quasi-compact, quasi-separated and locally of finite type, with
affine target, so the closed-immersion theorem
`IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map` descends each of the finitely
many conditions to a finitely generated subalgebra. An induction over the list of pairs `(i, j)` collects
them in one `T ⊇ s`; a closed immersion over a stage stays one over a larger stage
(`isClosedImmersion_chartBC_of_fac`, base change along `Spec T ⟶ Spec T₁`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.eT`
- def `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.eS`
- lemma `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.eS_hom_mY`
- theorem `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.isClosedImmersion_iff`
- abbrev `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.chart`
- abbrev `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.chartBase`
- abbrev `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.chartBC`
- lemma `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.chartBC_fst`
- lemma `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.chartBC_snd`
- lemma `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.eq_chartBC`
- lemma `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.isPullback_stage`
- lemma `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.isClosedImmersion_chartBC_of_fac`
- theorem `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.isSeparated_snd_iff`
- theorem `P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map` (ported by the same task).
All modules also import `Mathlib`.
