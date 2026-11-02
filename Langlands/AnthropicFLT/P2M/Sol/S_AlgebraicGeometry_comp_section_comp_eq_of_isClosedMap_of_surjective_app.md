# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app`. Statement. `AlgebraicGeometry.comp_section_comp_eq_of_isClosedMap_of_surjective_app` (rigidity-type lemma): let
`p : X ⟶ B` be a closed map with a section `ε` and with `Γ(B, U) → Γ(X, p⁻¹ U)` surjective on affine opens,
and `f : X ⟶ Y` such that `f (ε (p x)) = f x` for every point `x`. Then `p ≫ ε ≫ f = f`.

Proof. The two morphisms agree on points; for an affine open `V` of `Y`, `f⁻¹ V` is `p⁻¹` of an open of `B`
(closedness of `p` and the point condition), and on it the ring maps `Γ(V) → Γ(X, ·)` agree because every
section over `p⁻¹ U` is pulled back from `B` (surjectivity) and `ε ≫ p = 𝟙` (`appLE_self_eq_id_of_eq_id`,
`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.SolRigidityBase.appLE_self_eq_id_of_eq_id`
- theorem `P2MW.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.SolRigidityBase.main`
- theorem `P2MW.S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
