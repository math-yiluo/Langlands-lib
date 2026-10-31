# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd`

Ported module of the proof submitted by task `e36ae7da-512e-4a4d-a902-71146c92ec82` (descent of properness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `ProperDesc`). Apply the Chow-type theorem
`exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated` to `f`: `π : X' ⟶ X` proper surjective,
`j : X' ⟶ P` an open immersion, `q : P ⟶ Spec A₀` proper, `j ≫ q = π ≫ f`. For a base change
`ι' : Y ⟶ Spec A₀`, the open immersion `jY : P_Y ×_P X' → P_Y` has image the preimage of `U = j(X')`, and
the induced map `ρ` to `X_Y` is proper and surjective (`isPullback_ρ`). If `X_Y → Y` is proper, the image of
`jY` is closed (`isClosed_range_jY`); conversely, if it is closed then `jY` is a closed immersion, so
`X'_Y → Y` is proper and `X_Y → Y` is universally closed (`UniversallyClosed.of_comp_surjective`), hence
proper (`isProper_snd_of_isClosed_range`). So it suffices to make the preimage of `U` closed in `P_T` for
some stage. Over `A`, the preimage `U_A` of `U` is open and closed, so its complement `Z` is a quasi-compact
open of `P_A`. With `P_A` the limit of the `P_T` (`SubalgebraStages.nonempty_isLimit_cone`, module of task
80ab0ad1), Mathlib's `exists_preimage_eq` descends `Z` to a quasi-compact open `W` of some stage, and two
applications of `exists_map_preimage_eq_map_preimage` give a later stage `T` where `U_T ∩ W_T = ∅` and
`U_T ∪ W_T` is everything. Then `U_T` is the complement of an open, hence closed.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.jY`
- abbrev `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.σY`
- def `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.ρ`
- lemma `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.ρ_fst`
- lemma `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.ρ_snd`
- lemma `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.isPullback_ρ`
- scoped instance `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.surjective_ρ`
- scoped instance `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.isProper_ρ`
- lemma `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.range_jY`
- lemma `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.isClosed_range_jY`
- lemma `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.ProperDesc.isProper_snd_of_isClosed_range`
- theorem `P2MW.S_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SubalgebraStages` (port of task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone` (port of task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated` (ported by this task).
All modules also import `Mathlib`.
