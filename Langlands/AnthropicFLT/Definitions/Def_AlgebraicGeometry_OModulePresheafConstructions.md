# Constructions on presheaves of modules: products, kernels, images, cokernels, pushforward, dévissage

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`, in
namespace `AlgebraicGeometry`. All objects live in a fixed universe `u`. Throughout, `π : V ⟶ Spec R`
for a commutative ring `R`, and `OModulePresheaf π`, `Hom`, `AffHom`, `SES` and `AffSES` are the notions
of `Def_AlgebraicGeometry_OrderedAffineCoverCech` and `Def_AlgebraicGeometry_OModulePresheafHom`.

## Definitions

**Covers.** `K.preimage i`, for a closed immersion `i : Z ⟶ V` and an ordered affine cover `K` of `V`,
is the ordered affine cover of `Z` by the preimages `i⁻¹(U j)` (`preimage_U`).

**Basic constructions.** For presheaves `F`, `G` over `π`:

- `F.prod G` is the product presheaf `U ↦ F(U) × G(U)`, with projections `fstHom` and `sndHom`;
- `F.pow n` is the `n`-fold power `U ↦ (Fin n → F(U))`;
- `zero π` is the zero presheaf `U ↦ PUnit` (its sections are a subsingleton);
- `F.restrOpen W₀`, for an open `W₀`, is the presheaf `U ↦ F(U ⊓ W₀)`, with `Γ(V, U)` acting through
  restriction to `U ⊓ W₀`.

**Kernels, images and cokernels.** For `φ : Hom F G`:

- `ker φ`, `im φ` and `coker φ` are the presheaves `U ↦ ker (φ U)`, `U ↦ im (φ U)` and
  `U ↦ G(U) / im (φ U)`, with the induced module structures (`submoduleSections`,
  `cokerModuleSections`) and restriction maps; `ker_smul_mem` and `range_smul_mem` check that kernel and
  image are stable under `Γ(V, U)`;
- `kerImSES φ` is the short exact sequence `0 → ker φ → F → im φ → 0`, and `imCokerSES φ` is
  `0 → im φ → G → coker φ → 0`.

**Pushforward.** For a morphism `i : Z ⟶ V` and a presheaf `H` over `i ≫ π`:

- `pushforward π i H` is the presheaf `U ↦ H(i⁻¹ U)` over `π`, with `Γ(V, U)` acting through
  `i.appLE U (i⁻¹ U)`. `appLE_algebraMap` (theorem) checks that this action is compatible with the
  `R`-algebra structures;
- `pushforwardUnit π i` is the pushforward of the structure presheaf of `Z`.

**Trivial short exact sequences.** `AffHom.zeroFrom F` and `AffHom.zeroTo F` are the zero morphisms
from and to `zero π`. `AffSES.zeroLeft F` is the affine short exact sequence `0 → 0 → F → F → 0`.
`AffHom.powOne F` is the isomorphism `F.pow 1 → F`, and `AffSES.powOne F` is the affine short exact
sequence `0 → F.pow 1 → F → 0 → 0`.

**Dévissage.** Let `F` be a presheaf over `π` and `Y` a closed subset of `V`. A `F.DevissageStep Y`
consists of:

- a nonempty closed subset `Z₀ ⊆ Y` whose reduced closed subscheme (the subscheme of the vanishing ideal
  of `Z₀`) is integral;
- a presheaf `H` on that subscheme whose pushforward to `V` is coherent, quasi-coherent and supported in
  `Z₀`;
- a presheaf `G₃` over `π` with an affine short exact sequence `0 → pushforward H → F → G₃ → 0`;
- a closed subset `Z₁` strictly smaller than `Y` such that `G₃` is coherent, quasi-coherent and supported
  in `Z₁`.

`HasDevissageStep` is the proposition: for every noetherian ring `R`, every separated morphism
`π : V ⟶ Spec R` from a noetherian scheme `V`, every coherent quasi-coherent `F` over `π` supported in a
nonempty closed subset `Y` and annihilated, on every affine open `U`, by the vanishing ideal of `Y` on
`U`, there is a dévissage step of `F` for `Y`.

The remaining declarations are unfolding lemmas (`prod_obj`, `fstHom_app`, `sndHom_app`, `pow_obj`,
`pow_res_apply`, `restrOpen_obj`, `restrOpen_res`, `ker_obj`, `im_obj`, `coker_obj`, `ker_res_coe`,
`im_res_coe`, `coker_res_mk`, `ker_smul_coe`, `im_smul_coe`, `coker_smul_mk`, `kerImSES_inc_app`,
`kerImSES_proj_app`, `imCokerSES_inc_app`, `imCokerSES_proj_app`, `pushforward_obj`, `pushforward_res`,
`pushforward_smul`) and the instance that the sections of `zero π` form a subsingleton.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OModulePresheafConstructions.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafHom` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
