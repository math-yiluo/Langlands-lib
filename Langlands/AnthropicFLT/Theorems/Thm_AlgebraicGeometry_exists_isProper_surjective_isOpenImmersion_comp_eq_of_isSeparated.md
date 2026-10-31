# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated`

Ported module of the proof submitted by task `e36ae7da-512e-4a4d-a902-71146c92ec82` (descent of properness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.solution` applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

States the same conclusion as the integral case without assuming `X` integral: for a noetherian ring `A`
and a separated, quasi-compact morphism `f : X ⟶ Spec A` locally of finite type, there are `X'`, `P`,
`π : X' ⟶ X` proper and surjective, `j : X' ⟶ P` an open immersion and `q : P ⟶ Spec A` proper with
`j ≫ q = π ≫ f`. The proof term applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated` (ported by this task).
All modules also import `Mathlib`.
