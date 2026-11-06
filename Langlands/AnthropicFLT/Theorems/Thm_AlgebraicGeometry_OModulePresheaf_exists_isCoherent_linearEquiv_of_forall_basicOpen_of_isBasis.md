# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.solution π B hdown hcov M res res_smul res_refl res_comp hqc hfg`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`: let
`R` be a commutative ring, `π : V ⟶ Spec R`, and `B` a set of affine opens of `V` that is closed under passing to
smaller affine opens (`hdown`) and covers `V` (`hcov`). Let `M W` (`W ∈ B`) be finite `Γ(V, W)`-modules (`hfg`) that
are `R`-modules compatibly (scalar tower), with restriction maps `res` that are semilinear (`res_smul`), unital and
transitive (`res_refl`, `res_comp`), and quasi-coherent in the sense that for `W_g = D(g) ⊆ W` restriction
`M W → M W_g` is a localization at `g` (`hqc`: `g^n`-multiples lift and elements killed by restriction are killed by
a power of `g`). Then there are a coherent quasi-coherent FLT presheaf `G` over `π` and `R`-linear isomorphisms
`e W : G(W) ≅ M W` for `W ∈ B`, semilinear and compatible with restriction, such that for every quasi-coherent `F`
over `π`: compatible semilinear families `θ W : M W → F(W)` come from a unique `Φ : AffHom G F` (with
`Φ = θ ∘ e` on members), and compatible semilinear families `ϑ W : F(W) → M W` come from a unique
`Ψ : AffHom F G` (with `e ∘ Ψ = ϑ` on members).

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis` (same contribution).
Other imports: `Mathlib`.
