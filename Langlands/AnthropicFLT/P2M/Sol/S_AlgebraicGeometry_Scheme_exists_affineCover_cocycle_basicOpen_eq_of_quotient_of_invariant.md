# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.lean` (SHA-256 `51d4e63f66f7a93cec0cc4557038382194a2ef619f704ac3a8c6d8e3ea395b85`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT text writes `(ρ γ).hom` for the morphism underlying an automorphism `ρ γ : Aut X`, as in the Mathlib that FLT uses, where `Aut X` is `X ≅ X`. In the Library's Mathlib `CategoryTheory.Aut X` is a structure whose underlying isomorphism is the field `asIso`, so each of the 12 occurrences of `(ρ …).hom` is written `(ρ …).asIso.hom`. Both denote the same morphism; nothing else in the statements and proofs is changed by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`.

Statement. `AlgebraicGeometry.Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`: let
a group `Γ` act on a scheme `X` through `ρ : Γ →* Aut X` and let `q : X ⟶ Y` be a morphism with
`(ρ γ) ≫ q = q` for every `γ`, such that `q` is surjective, `q.app V` is injective for every open `V` of
`Y` with image the sections over `q ⁻¹ᵁ V` invariant under every `ρ γ`, and every affine open of `X`
invariant under every `ρ γ` is `q ⁻¹ᵁ V` for an affine open `V` of `Y`. Let `U i` (`i : Fin r`) be an
invariant affine open cover of `X` with an invariant cocycle `w i j ∈ Γ(X, U i)` (`w i i = 1`, the cocycle
identity on `U i ⊓ U j`, `X.basicOpen (w i j) = U i ⊓ U j`). Then there are affine opens `V i` of `Y`
with `q ⁻¹ᵁ V i = U i`, covering `Y`, and sections `v i j ∈ Γ(Y, V i)` with `v i i = 1`, the cocycle
identity on `V i ⊓ V j` and `Y.basicOpen (v i j) = V i ⊓ V j`, whose pullbacks along `q` are the
`w i j`.

Proof. The opens `V i` are given by the descent hypothesis on invariant affine opens. Each `w i j` is
invariant, so after restriction along `q ⁻¹ᵁ V i = U i` it lies in the image of `q.app (V i)`; this gives
`v i j` with `q.appLE (V i) (U i) _ (v i j) = w i j`. The pullback `q.appLE` over `V i ⊓ V j` is injective
(`QPB.appLE_injective`), so the unit and cocycle identities for `v` follow from those for `w`. The `V i`
cover `Y` because `q` is surjective and the `U i` cover `X`; and
`Y.basicOpen (v i j) = V i ⊓ V j` because both sides have preimage `U i ⊓ U j` under the surjective `q`
(`Scheme.basicOpen_appLE`, `QPB.preimage_injective`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.rO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.rO_rO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.rO_refl`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.rO_rO_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.preimage_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.rO_appLE`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.appLE_rO`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.QPB.appLE_injective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Langlands.MathlibBase`.
