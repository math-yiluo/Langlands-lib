# Sections of a locally trivial module over an affine open commute with affine base change

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial` states under its FLT name.

## Statement

Let `R` be a commutative ring in universe `u`, `c : X ⟶ Spec R` a morphism,
`M` a locally trivial sheaf of modules on `X` (every point has an open
neighbourhood on which the pullback of `M` is isomorphic to the structure
sheaf), `U` an affine open of `X` and `A` an `R`-algebra. Write
`X_A = X ×_{Spec R} Spec A`, `p : X_A ⟶ X` for the first projection and `M_A`
for the pullback of `M` along `p`. Sections over `U` are an `R`-module through
`c`, and sections over `p⁻¹ U` an `A`-module through the second projection.
Then there is an `A`-linear isomorphism
`e : A ⊗_R Γ(M, U) ≅ Γ(M_A, p⁻¹ U)` with `e (1 ⊗ m)` equal to the pullback of
`m` (its image under the unit of `Scheme.Modules.pullbackPushforwardAdjunction p`).

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names), `p2m_reactivate` by `open scoped`; a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Let `B = Γ(X, U)`, an `R`-algebra through `c`, `i : Spec B ⟶ X` the inclusion
of `U` (`IsAffineOpen.fromSpec`) and `φ : B → B ⊗_R A` the first inclusion.

1. Affine charts. The preimage `p⁻¹ U` is isomorphic to `Spec (B ⊗_R A)`
   (`pullbackAffineOpenIsoSpecTensor`, with the ring isomorphism `algEquiv`),
   giving an open immersion `j : Spec (B ⊗_R A) ⟶ X_A` with image `p⁻¹ U` and
   `j ≫ p = Spec φ ≫ i` (`j_fst`).
2. Sections through the charts. For open immersions, the unit of the
   pullback–pushforward adjunction is bijective on opens inside the image
   (`UnitCalculus.bijective_unit_app_of_isOpenImmersion`), so
   `Γ(M, U) ≅ Γ(i^* M)` (`ρ`) and `Γ(M_A, p⁻¹ U) ≅ Γ(j^* M_A)` (`θ`). By the
   compatibility of pullback with composition,
   `j^* M_A ≅ (Spec φ)^* (i^* M)` (`σ`).
3. Quasi-coherence. The pullback `i^* M` is locally trivial on `Spec B`
   (`locallyTrivial_pullback`), so it is the sheaf associated with its global
   sections `N'` (`Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial`, in
   this port), and its sections commute with the base change `φ`:
   `(B ⊗_R A) ⊗_B N' ≅ Γ((Spec φ)^* (i^* M))`
   (`Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma`, in this
   port).
4. Tensor algebra. `(B ⊗_R A) ⊗_B N' ≅ A ⊗_R N'` by cancelling `B`
   (`κ`, with explicit inverse maps `Kfwd`, `Kbwd`), and `N' ≅ Γ(M, U)`
   `B`-linearly by step 2 (`ρlin`).
5. Composing these isomorphisms gives `e` (`e₀`). It is `A`-linear because the
   `A`-module structure on `Γ(M_A, p⁻¹ U)` corresponds to multiplication by
   `1 ⊗ a` in `B ⊗_R A` (`scalar_key`), and the value on `1 ⊗ m` is computed by
   following `m` through the units of the adjunctions (`chase`).
