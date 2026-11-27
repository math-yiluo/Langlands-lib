# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.lean` (SHA-256 `b9c691f7b81330064eb00d426a71f18c7582e820e0f015dfe1d299cd2fa5d610`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.solution B X πX hQP Γ ρ hρ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- The FLT text writes `(ρ γ).hom` for the morphism underlying an automorphism `ρ γ : Aut X`, as in the Mathlib that FLT uses, where `Aut X` is `X ≅ X`. In the Library's Mathlib `CategoryTheory.Aut X` is a structure whose underlying isomorphism is the field `asIso`, so each of the 3 occurrences of `(ρ …).hom` is written `(ρ …).asIso.hom`. Both denote the same morphism; nothing else in the statements and proofs is changed by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`:
let `B` be a commutative ring, `X` a quasi-compact scheme and `πX : X ⟶ Spec B` a morphism that is an
immersion into some `Proj` of the polynomial ring `B[x₀, …, x_m]` followed by its structure morphism
`ProjSpace.π B m`, and let a finite group `Γ` act on `X` over `Spec B` through `ρ : Γ →* Aut X`. Then
`X` has a finite cover by affine opens `U i` (`i : Fin r`), each invariant under every `ρ γ`, with sections
`w i j ∈ Γ(X, U i)` satisfying `w i i = 1`, the cocycle identity on `U i ⊓ U j` and
`X.basicOpen (w i j) = U i ⊓ U j`, and invariant under every `ρ γ`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`, `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`.
Other imports: `Langlands.MathlibBase`.
