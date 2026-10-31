# Frames pull back

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.bijective_smul_unit_app_of_bijective_smul`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul` states under its FLT name.

## Statement

Let `p : X' ⟶ X` be a morphism of schemes, `M` a sheaf of modules on `X`,
`σ` a global section of `M` and `V` an open of `X`. Suppose `σ` is a frame
on `V`: for every open `W ≤ V`, the map `Γ(X, W) → Γ(M, W)`,
`g ↦ g • σ|W`, is bijective. Let `σ'` be the image of `σ` in the global
sections of `p^* M` under the unit `M ⟶ p_* p^* M` of
`Scheme.Modules.pullbackPushforwardAdjunction p`. Then `σ'` is a frame on
`p⁻¹ V`: for every open `W' ≤ p⁻¹ V`, the map `g ↦ g • σ'|W'` from
`Γ(X', W')` to the sections of `p^* M` over `W'` is bijective.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names), `p2m_reactivate` by `open scoped`; a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

1. A global section `s` of a sheaf of modules `N` on a scheme `Z` defines a
   morphism `smulHom N s` from the structure sheaf to `N`, given on an open
   `W` by `g ↦ g • s|W`. If `s` is a frame on `V`, the restriction of
   `smulHom N s` to `V` is an isomorphism: by
   `Scheme.Modules.Hom.isIso_iff_isIso_app`, it suffices that its components
   over the opens `V.ι(W)` are bijective, which is the hypothesis. Through
   `Scheme.Modules.restrictFunctorIsoPullback`, the pullback of
   `smulHom N s` along `V.ι` is an isomorphism as well.
2. The pullback of `smulHom M σ` along `p` is, up to the isomorphism
   `p^* 𝒪_X ≅ 𝒪_{X'}` (`SheafOfModules.pullbackObjUnitToUnit`), the morphism
   `smulHom (p^* M) σ'`. The proof compares the adjoint morphisms
   `𝒪_X ⟶ p_* p^* M` under the pullback–pushforward adjunction: both send a
   function `g` on `W` to `p^♯(g) • σ'|p⁻¹W`, using that the unit is linear
   (`Scheme.Modules.Hom.app_smul`) and commutes with restriction
   (`SheafOfModules.unitToPushforwardObjUnit_val_app_apply`,
   `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`).
3. The open immersion `(p⁻¹ V).ι` followed by `p` equals the restriction
   `p ∣_ V` followed by `V.ι` (`morphismRestrict_ι`). Since pullback is
   compatible with composition (`Scheme.Modules.pullbackComp`,
   `Scheme.Modules.pullbackCongr`), the pullback of `smulHom M σ` along `p`
   and then `(p⁻¹ V).ι` is the pullback along `p ∣_ V` of its pullback along
   `V.ι`, which is an isomorphism by step 1. By step 2, so is the pullback of
   `smulHom (p^* M) σ'` along `(p⁻¹ V).ι`.
4. Reading this isomorphism on the open `(p⁻¹ V).ι⁻¹ W'` of `p⁻¹ V`, whose
   image in `X'` is `W'`, gives the bijectivity of
   `g ↦ g • σ'|W'`.
