# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.solution q p G₁ G₂ hq₁ hq₂ G'₁ hq'₁ η₁ hη₁s hη₁V hη₁U hβ₁ G'₂ hq'₂ η₂ hη₂s hη₂V hη₂U hβ₂ ψ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct`:
let `A` be a commutative ring, `q : P ⟶ Spec A`, `p : V' ⟶ P`, `G₁, G₂` quasi-coherent FLT presheaves over `q`, and
`G'₁, G'₂` quasi-coherent presheaves over `p ≫ q` that are pullbacks of `G₁, G₂` in the sense of the ported theorem
`IsQuasicoherent.exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom`: maps
`η_i U V h : G_i(U) → G'_i(V)` (for affine `V ⊆ p⁻¹ U`) that are semilinear (`hη₁s`, `hη₂s`), compatible with
restriction in `V` and in `U` (`hη₁V`, `hη₁U`, `hη₂V`, `hη₂U`), and induce isomorphisms
`Γ(V', V) ⊗_{Γ(P, U)} G_i(U) ≅ G'_i(V)` (`hβ₁`, `hβ₂`). Then every `ψ : AffHom G₁ G₂` has a pullback
`ψ' : AffHom G'₁ G'₂` with `ψ' ∘ η₁ = η₂ ∘ ψ`; `ψ'` is surjective on affines if `ψ` is, and if moreover
`ker (ψ.app U) = J • ⊤` on all affines for an ideal `J ⊆ A`, then `ker (ψ'.app V) = J • ⊤` on all affines.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_of_forall_exists_linearEquiv_tensorProduct` (same contribution).
Other imports: `Mathlib`.
