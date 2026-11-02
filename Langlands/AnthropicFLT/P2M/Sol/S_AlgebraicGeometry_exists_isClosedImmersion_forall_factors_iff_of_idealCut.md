# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut`. Statement. `AlgebraicGeometry.exists_isClosedImmersion_forall_factors_iff_of_idealCut`: let `Q` be a property of affine points
`Spec A ⟶ H` that is stable under base change, local for Zariski covers `{Spec A_{r_i}}` and cut out by an ideal on
each affine open (for `Spec B ≅ U` there is `J ⊆ B` with `Q(Spec φ ≫ U) ↔ φ(J) = 0`). Then there is a closed
immersion `C ⟶ H` such that an affine point satisfies `Q` exactly when it factors through `C`.

Proof. The ideal cutting out `Q` on an affine open is unique (local `ideal_eq_of_forall_map_eq_bot_iff`, testing with
the quotient map), so the ideals agree on overlaps and form an ideal sheaf; its closed subscheme `C` is given by the
ported `Scheme.exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot`. A point factors through `C` iff
the pulled-back ideal vanishes, which is checked on a Zariski cover by the ported
`Ideal.exists_forall_iff_map_eq_bot_of_forall_away` together with the locality of `Q`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.P2mWs30CS1.ideal_eq_of_forall_map_eq_bot_iff`
- theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.P2mWs30CS1.specMap_ofHom_comp`
- theorem `P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Ideal_exists_forall_iff_map_eq_bot_of_forall_away` (same contribution).
Other imports: `Mathlib`.
