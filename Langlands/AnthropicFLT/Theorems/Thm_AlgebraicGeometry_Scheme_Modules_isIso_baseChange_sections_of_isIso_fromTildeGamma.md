# Global sections of a quasi-coherent module on an affine scheme commute with affine base change

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma` proves the theorem `AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma`.

## Statement

Let `φ : R ⟶ S` be a morphism of commutative rings in universe `u` and `M` a
sheaf of modules on `Spec R` such that `M.fromTildeΓ`, the canonical morphism
from the sheaf associated with the `R`-module of global sections `Γ(M)` to
`M`, is an isomorphism. Consider the `R`-linear map from `Γ(M)` to the
global sections of the pullback `(Spec φ)^* M`, viewed as an `R`-module by
restriction of scalars: the global sections of the unit
`M ⟶ (Spec φ)_* (Spec φ)^* M` of `Scheme.Modules.pullbackPushforwardAdjunction`,
followed by the identification `Scheme.Modules.pushforwardSpecCompΓIso φ`
(port module `Definitions/Def_AlgebraicGeometry_ModulesTildePullback`) of
global sections of a pushforward with restriction of scalars. Its adjoint
under `ModuleCat.extendRestrictScalarsAdj φ` is an `S`-linear base change map
`S ⊗_R Γ(M) ⟶ Γ((Spec φ)^* M)`. This map is an isomorphism.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma`, which has the same statement. The Markdown of that module outlines the argument.
