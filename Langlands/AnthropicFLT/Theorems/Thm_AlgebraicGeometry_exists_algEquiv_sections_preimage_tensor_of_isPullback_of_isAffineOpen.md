# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.solution K f H fB π hB`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen`: let
`f : A ⟶ Spec K`, `H` a `K`-algebra, and `B` with `fB : B ⟶ Spec H` and `π : B ⟶ A` forming a pullback
square of `f` and `Spec (K → H)`. Give all rings of sections their `K`-algebra structures through `f` and
`π ≫ f`. Then there are `K`-algebra isomorphisms `ε V : Γ(B, π⁻¹ V) ≃ Γ(A, V) ⊗[K] H` for affine opens `V` of
`A` such that `π⁻¹ V` is affine, `ε V (π^* a) = a ⊗ 1`, `ε V` sends the image of `h : H` (through `fB`) to
`1 ⊗ h`, and for affine `V' ≤ V` the isomorphisms commute with restriction
(`(restriction ⊗ id) ∘ ε V = ε V' ∘ restriction`).

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_algEquiv_sections_preimage_tensor_of_isPullback_of_isAffineOpen` (same contribution).
Other imports: `Mathlib`.
