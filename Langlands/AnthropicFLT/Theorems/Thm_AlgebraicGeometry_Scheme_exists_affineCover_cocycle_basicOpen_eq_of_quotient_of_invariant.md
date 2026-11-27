# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.lean` (SHA-256 `6adea0772f76bf89d2d57412d72db4049f5a505319b98037aee59c0772f443f5`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.solution X Y Γ ρ q hq hsurj hinj hrange hdesc r U hUaff hinv hcov w hw1 hw2 hw3 hw4`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- The FLT text writes `(ρ γ).hom` for the morphism underlying an automorphism `ρ γ : Aut X`, as in the Mathlib that FLT uses, where `Aut X` is `X ≅ X`. In the Library's Mathlib `CategoryTheory.Aut X` is a structure whose underlying isomorphism is the field `asIso`, so each of the 5 occurrences of `(ρ …).hom` is written `(ρ …).asIso.hom`. Both denote the same morphism; nothing else in the statements and proofs is changed by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

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

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_affineCover_cocycle_basicOpen_eq_of_quotient_of_invariant`.
Other imports: `Langlands.MathlibBase`.
