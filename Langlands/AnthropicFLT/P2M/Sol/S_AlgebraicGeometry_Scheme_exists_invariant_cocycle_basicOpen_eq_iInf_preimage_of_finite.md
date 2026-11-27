# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.lean` (SHA-256 `450854c0e3ec792dbc6b9948840ea8a02b349de79f368b979d5f6bf7a2d5c8ef`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT text writes `(ρ γ).hom` for the morphism underlying an automorphism `ρ γ : Aut X`, as in the Mathlib that FLT uses, where `Aut X` is `X ≅ X`. In the Library's Mathlib `CategoryTheory.Aut X` is a structure whose underlying isomorphism is the field `asIso`, so each of the 26 occurrences of `(ρ …).hom` is written `(ρ …).asIso.hom`. Both denote the same morphism; nothing else in the statements and proofs is changed by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite`.

Statement. `AlgebraicGeometry.Scheme.exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite`: let a
finite group `Γ` act on a scheme `X` through `ρ : Γ →* Aut X`, and let `w i j ∈ Γ(X, U i)`
(`i j : Fin r`) satisfy `w i i = 1`, the cocycle identity on `U i ⊓ U j` and
`X.basicOpen (w i j) = U i ⊓ U j`. Then the opens `U' i = ⨅ γ, (ρ γ) ⁻¹ᵁ U i` are invariant under every
`ρ γ`, and there are sections `w' i j ∈ Γ(X, U' i)` with the same three properties which are invariant:
the pullback of `w' i j` along `ρ γ` is `w' i j` for every `γ`.

Proof. `U' i` is the finite infimum of the translates of `U i`, and `w' i j` is the product over `γ` of
the pullbacks of `w i j` along `ρ γ`, restricted to `U' i` (a norm). The unit and cocycle identities hold
factor by factor (`K3Aux.map_appLE_apply`, `K3Aux.appLE_map_apply`). The basic open of the product is the
intersection of the basic opens of the factors (`K3Aux.basicOpen_finset_prod`), which is
`U' i ⊓ U' j`. Invariance of `U' i` and of `w' i j` under `ρ δ` comes from reindexing the infimum and the
product along `γ ↦ γ * δ` (`Fintype.prod_equiv`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.K3Aux.mem_finset_inf`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.K3Aux.preimage_finset_inf`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.K3Aux.basicOpen_finset_prod`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.K3Aux.hom_appLE_congr`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.K3Aux.map_appLE_apply`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.K3Aux.appLE_map_apply`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.K3Aux.appLE_appLE_apply`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Langlands.MathlibBase`.
