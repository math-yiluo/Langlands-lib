# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen`.

Proof. Namespace `SbBody`: `appLE_self_of_eq_id` (`h.appLE U U = 𝟙` when `h = 𝟙`) and `appLE_congr_hom`.
`solution`: the ported theorem `AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen`
gives the isomorphisms `ε₀` for the chosen pullback `pullback f g` (with `g := Spec (K → H)`), with the same
four properties. The pullback square `hB` gives an isomorphism `e : B ≅ pullback f g` over `A` and
`Spec H` (`hB.isoPullback`). Its `appLE` maps give ring isomorphisms `θ V` between the sections of the two
schemes over the preimages of `V` (`hθ1`, `hθ2`), compatible with the `K`-algebra structures, with the maps
from `A` and from `Spec H`, and with restriction (`hθK`, `hθfst`, `hθsnd`, `hθnat`). Then
`ε V := ε₀ V ∘ (θ V)⁻¹`; affineness of `π⁻¹ V` follows from that of the preimage in the chosen pullback, and the
other three properties transport along `θ`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.SbBody.appLE_self_of_eq_id`
- theorem `P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.SbBody.appLE_congr_hom`
- theorem `P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen` (Library).
Other imports: `Mathlib`.
