# A locally trivial module on an affine scheme is the sheaf of its global sections

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial` states under its FLT name.

## Statement

Let `R` be a commutative ring in universe `u` and `M` a sheaf of modules on
`Spec R`. Suppose `M` is locally trivial: every point `x` has an open
neighbourhood `V` such that the pullback of `M` along the inclusion `V.ι` is
isomorphic to the structure sheaf `SheafOfModules.unit` of `V`. Then the
canonical morphism `M.fromTildeΓ` from the sheaf associated with the
`R`-module of global sections `Γ(M)` to `M` is an isomorphism. So `M` is
quasi-coherent, and determined by its global sections.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

The proof combines two results of the port. By
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen`,
it suffices that for every `g ∈ R` the restriction map from the global
sections to the sections over the basic open `D(g)` is a localization at the
powers of `g`. This is
`AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial`,
applied to the affine open `⊤` of `Spec R` and the local trivializations.
