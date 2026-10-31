# Sections over an affine open of a flat scheme over a ring are flat

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat.solution`. Its statement is that of `AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat` states under its FLT name.

## Statement

Let `R` be a commutative ring in universe `u`, `X` a scheme and
`c : X ⟶ Spec R` a flat morphism. Let `U` be an affine open of `X`. Give
`Γ(X, U)` the `R`-algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom c U`,
induced by `c` and the identification `Γ(Spec R, ⊤) ≅ R`. Then `Γ(X, U)` is a
flat `R`-module.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

Flatness is a property of morphisms that is affine-local
(`HasRingHomProperty`), so the ring map
`c.appLE ⊤ U : Γ(Spec R, ⊤) ⟶ Γ(X, U)` between the sections over the affine
opens `⊤` and `U` is flat. The inverse of `Scheme.ΓSpecIso R` is a ring
isomorphism, hence flat (`RingHom.Flat.of_bijective`). Their composite is
flat (`RingHom.Flat.comp`), and it is the algebra map of the given algebra
structure, so `RingHom.flat_algebraMap_iff` turns it into flatness of the
module.
