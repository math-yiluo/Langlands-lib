# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 14 here); in 1 line the replacements `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField`. Statement. `AlgebraicGeometry.bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField`: let
`h : Z ⟶ X` be a morphism over `Y` (`h ≫ q = p`) inducing an isomorphism of the fibres over a point `y`. For
affine opens `W ∋ y` of `Y`, `U ⊆ q⁻¹ W` of `X` with `h⁻¹ U` affine, the map `Γ(X, U) → Γ(Z, h⁻¹ U)` becomes
bijective after tensoring with the residue field `κ(y)` over `Γ(Y, W)`.

Proof. For affine opens the fibre over `y` of `Spec Γ(X, U)` is `Spec (Γ(X, U) ⊗ κ(y))` (pullback of affine
schemes), and similarly for `Z`; the isomorphism of fibres restricts to these affine pieces, and the induced
ring map is the base change of `Γ(X, U) → Γ(Z, h⁻¹ U)`, which is therefore bijective.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
