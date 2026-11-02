# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range`. Statement. `Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range`: over a noetherian ring `R`,
let `C` be a bounded complex of flat modules with `ker d₀` finite, exact in positive degrees after inverting `g`. For
every `R`-algebra `A` in which `g` is a unit, `ker (d₀ ⊗ A)` is finite projective, `C ⊗ A` is exact in positive
degrees and `A ⊗ ker d₀ → ker (d₀ ⊗ A)` is bijective.

Proof. Over `S = R_g` the ported `Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range` applies:
the kernel is flat and finitely presented (noetherian), hence projective, and its formation commutes with base
change. An algebra `A` with `g` invertible is an `S`-algebra, and the statements are transported from `S` to `A`
(sections `Transport`, `Cancel`, `FlatKer`, `Key`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.ker_le_range_transport`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.cancelBaseChange_baseChange_baseChange`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.baseChange_subtype_injective`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.exists_baseChange_subtype_eq`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.kerBaseChangeHom_bijective`
- def `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.kerEquiv`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.kerEquiv_apply_coe`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.key`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL.subsingleton_tensor`
- theorem `P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech` (Library), `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range` (same contribution).
Other imports: `Mathlib`.
