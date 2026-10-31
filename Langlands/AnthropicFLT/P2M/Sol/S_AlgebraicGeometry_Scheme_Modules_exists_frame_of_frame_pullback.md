# A section of an invertible sheaf that is a frame after pullback is a frame near the image point

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback` states under its FLT name.

## Statement

Let `p : X' ⟶ X` be a morphism of schemes, `M` an invertible sheaf of modules
on `X` (the port's `Scheme.Modules.IsInvertible`), `m` a global section of
`M` and `z` a point of `X'`. Let `m'` be the image of `m` in the global
sections of `p^* M` under the unit of
`Scheme.Modules.pullbackPushforwardAdjunction p`. Call a global section `s` a
frame on an open `U` if for every open `V ≤ U` the map `g ↦ g • s|V` from
functions on `V` to sections over `V` is bijective. If `m'` is a frame on some
open neighbourhood of `z`, then `m` is a frame on some open neighbourhood of
`p z`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

1. Choose an open `U ∋ p z` and a trivialization `e : M|U ≅ 𝒪_U`. The section
   `τ = e⁻¹(1)` is a frame of `M|U` on all of `U`, so the restriction of `m`
   to `U` is `h • τ` for a unique function `h` on `U`.
2. Restrict `p` to `p⁻¹ U ⟶ U`, written `pU`. Two applications of the
   compatibility of pullback with composition
   (`Scheme.Modules.unit_app_comp_pullbackComp_inv`, in this port) identify the
   pullback of `m'` to `p⁻¹ U` with the pullback of `m|U` along `pU`, by an
   isomorphism of modules; frames are transported by isomorphisms. Since
   frames pull back
   (`Scheme.Modules.bijective_smul_unit_app_of_bijective_smul`, in this
   port), the pullback of `m'` is a frame near `z`, so `pU^*(h) • pU^*(τ)` is
   a frame near `z`, while `pU^*(τ)` is a frame on all of `p⁻¹ U`.
3. If `T` is a frame on `U` and `H • T` is a frame on a smaller open `V`, then
   multiplication by `H` is bijective on functions on `V`, so `H` is a unit on
   `V`. Hence the germ of `pU^*(h)` at `z` is a unit. Germs are compatible
   with the stalk map of `pU` (`Scheme.Hom.germ_stalkMap`), and a local ring
   map reflects units, so the germ of `h` at `p z` is a unit.
4. Conversely, if `T` is a frame on `U` and the germ of `H` at a point is a
   unit, then `H • T` is a frame on the basic open of `H`, which contains the
   point: on any smaller open, `H` restricts to a unit
   (`RingedSpace.isUnit_res_basicOpen`), and multiplication by a unit is
   bijective. So `m|U = h • τ` is a frame on an open `V ∋ p z` of `U`.
5. Frames descend along the open immersion `U.ι`: for opens inside the image,
   the unit of the pullback–pushforward adjunction is bijective
   (`Scheme.Modules.bijective_unit_app_of_le_opensRange`, in this port) and so
   is `U.ι` on functions. Hence `m` is a frame on the image of `V` in `X`,
   which contains `p z`.
