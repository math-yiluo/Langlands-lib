# The adjunction unit of a composite pullback

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv` proves the theorem `AlgebraicGeometry.Scheme.Modules.unit_app_comp_pullbackComp_inv`.

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

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv`, which has the same statement. The Markdown of that module outlines the argument.
