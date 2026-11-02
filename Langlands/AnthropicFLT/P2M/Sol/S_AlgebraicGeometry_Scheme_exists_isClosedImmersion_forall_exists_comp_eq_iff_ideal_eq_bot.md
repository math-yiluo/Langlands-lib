# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot`. Statement. `AlgebraicGeometry.Scheme.exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot`: let `E` be a
scheme and `I` assign to every affine point `s : Spec R ⟶ E` an ideal of `R`, compatibly with base change
(`I (s ∘ Spec ψ) = ψ(I s)`). Then there is a closed immersion `Z ⟶ E` through which `s` factors iff `I s = 0`.

Proof. For each affine open `V` of `E`, the tautological point `Spec Γ(E, V) ⟶ E` gives the ideal
`J V = I(V.fromSpec)` (`idealOf`, `J`); compatibility with base change along restrictions makes these an
ideal sheaf (`idealOf_map`, `exists_theta`, `iSup_small_eq_top`). Let `Z` be its closed subscheme. A point
`s : Spec R ⟶ E` factors through `Z` iff the pullback of the ideal sheaf vanishes, which on the affine
pieces `ψV` of `s` is the extension of `J V`, i.e. `I` of the restricted point; by compatibility this is
`I s = 0` (`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.idealOf`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.idealOf_map`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.J`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.J_ideal`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.ψV`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.fromSpec_eq_specMap_ψV`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.exists_theta`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.iSup_small_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0.main`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
