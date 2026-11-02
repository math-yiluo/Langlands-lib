# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict`. Statement. `AlgebraicGeometry.bijective_app_of_bijective_appTop_morphismRestrict`: if the restriction `p ∣_ U` of
`p : X ⟶ B` over an open `U` has bijective map on global sections, then `p.app U : Γ(B, U) → Γ(X, p⁻¹ U)` is
bijective.

Proof. `p.app U` is identified with `(p ∣_ U).appTop` up to the canonical isomorphisms of sections of open
subschemes (`bijective_app_congr`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict.P4Aux.bijective_app_congr`
- theorem `P2MW.S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
