# The adjunction unit of a composite pullback

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.unit_app_comp_pullbackComp_inv`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv` states under its FLT name.

## Statement

Let `g : Z ⟶ Y` and `f : Y ⟶ X` be morphisms of schemes, `M` a sheaf of
modules on `X` and `U` an open of `X`. Write `η_h` for the unit of the
adjunction between pullback and pushforward along a morphism `h`, and
`pullbackComp g f : pullback f ⋙ pullback g ≅ pullback (g ≫ f)` for
Mathlib's comparison of iterated pullbacks. Then, on sections over `U`, the unit for `g ≫ f`
followed by the inverse of `pullbackComp g f` at `M` (on the open
`(g ≫ f)⁻¹ U`) equals the unit for `f` followed by the unit for `g` at the
pullback `f^* M` (on the open `f⁻¹ U`):

`(η_{g ≫ f} M)(U) ≫ ((pullbackComp g f).inv M)((g ≫ f)⁻¹ U) = (η_f M)(U) ≫ (η_g (f^* M))(f⁻¹ U)`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

The unit of the composite adjunction (pullback along `f`, then along `g`)
and the unit of the adjunction for `g ≫ f` are related by the conjugate of
`(pullbackComp g f).inv` (`unit_conjugateEquiv`). Mathlib's
`conjugateEquiv_pullbackComp_inv` identifies that conjugate with the
comparison of pushforwards. Evaluating the resulting identity of natural
transformations at `M` and then on the open `U`, and simplifying the
components of composite units and pushforward maps
(`Adjunction.comp_unit_app`, `pushforward_map_app`,
`pushforwardComp_hom_app_app`), gives the displayed equation.
