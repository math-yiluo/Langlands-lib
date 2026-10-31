# The pullback–pushforward unit along an open immersion is bijective inside its range

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.bijective_unit_app_of_le_opensRange`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange` states under its FLT name.

## Statement

Let `j : Y ⟶ X` be an open immersion of schemes, `N` a sheaf of modules on
`X` and `V` an open of `X` contained in the range `j.opensRange`. Then the
component on `V` of the unit `N ⟶ j_* j^* N` of the adjunction
`Scheme.Modules.pullbackPushforwardAdjunction j` is a bijective map
`Γ(N, V) → Γ(j^* N, j⁻¹ V)`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

For an open immersion, Mathlib also has the restriction adjunction
`restrictAdjunction j`. The two left adjoints are identified by the
isomorphism `leftAdjointUniq`, and `Adjunction.unit_leftAdjointUniq_hom_app`
expresses the unit of the restriction adjunction as the unit of
`pullbackPushforwardAdjunction j` followed by this isomorphism. On the open
`V`, the unit of the restriction adjunction is the restriction map of `N`
along `j(j⁻¹ V) ≤ V`. Because `V` lies in the range of `j`, `j(j⁻¹ V) = V`
(`Scheme.Hom.image_preimage_eq_opensRange_inf`), so this restriction map is
`N.presheaf.map` of an `eqToHom`, hence an isomorphism. Composing with the
component of `leftAdjointUniq` on `j⁻¹ V`, which is an isomorphism, shows
that the component of the unit is an isomorphism of modules, so it is
bijective (`ConcreteCategory.isIso_iff_bijective`).
