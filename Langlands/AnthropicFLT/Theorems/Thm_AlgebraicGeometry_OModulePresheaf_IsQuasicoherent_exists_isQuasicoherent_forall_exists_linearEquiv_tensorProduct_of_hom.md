# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.solution q p G hq`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom`:
let `A` be a commutative ring, `q : P ⟶ Spec A`, `p : V' ⟶ P`, and `G` a quasi-coherent FLT presheaf over `q`. Then
there are a presheaf `G'` over `p ≫ q` (the pullback `p^* G`) and `A`-linear maps `η U V h : G(U) → G'(V)` for affine
opens `U ⊆ P`, `V ⊆ V'` with `V ⊆ p⁻¹ U`, such that: `G'` is quasi-coherent, and coherent if `G` is; `η` is semilinear
along `p.appLE U V h` and compatible with restriction in `V` and in `U`; for every such `U, V` some
`Γ(V', V)`-linear isomorphism `β : Γ(V', V) ⊗_{Γ(P, U)} G(U) ≅ G'(V)` satisfies `β (1 ⊗ x) = η U V h x`; and `η W W'`
is bijective when `W' = p⁻¹ W` and `p` restricts to an isomorphism over `W`.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom` (same contribution).
Other imports: `Mathlib`.
