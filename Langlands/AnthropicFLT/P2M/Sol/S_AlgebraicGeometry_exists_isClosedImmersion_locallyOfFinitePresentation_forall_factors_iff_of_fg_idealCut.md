# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut`. Statement. `AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut`: the same
statement when the cutting ideals are finitely generated; the closed immersion is then also locally of finite
presentation.

Proof. Take `C` from the ported `exists_isClosedImmersion_forall_factors_iff_of_idealCut`. On each affine open
`U ≅ Spec B`, the restriction of `C` is `Spec (B / J)` with `J` the (unique, hence finitely generated) cutting
ideal, so `B → B/J` is of finite presentation (local `finitePresentation_app_of_fg_cut`,
`finitePresentation_map_of_isAffineOpen`); finite presentation is local on the target.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut.P2mWs11CS1p.finitePresentation_app_of_fg_cut`
- theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut.P2mWs11CS1p.finitePresentation_map_of_isAffineOpen`
- theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut` (same contribution).
Other imports: `Mathlib`.
