# Global sections of a quasi-coherent module on an affine scheme commute with affine base change

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

Write `unitΓ M` for the `R`-linear map above and `baseChangeΓ M` for its
adjoint.

1. `baseChangeΓ` is natural in `M`: this follows from the naturality of the
   unit of the pullback–pushforward adjunction, of
   `pushforwardSpecCompΓIso φ` and of the counit of the extension–restriction
   adjunction.
2. For the sheaf `N~` associated with an `R`-module `N`, the compatibility
   `tilde.pullbackSpecIso_unit` (in this port) gives
   `S ⊗ η_N ≫ baseChangeΓ (N~) ≫ Γ(e) = η'_{S ⊗ N}`, where `η` and `η'` are
   the units of the tilde adjunctions on `Spec R` and `Spec S` and `e` is the
   base-change isomorphism `tilde.pullbackSpecIso φ N`. The units of the tilde
   adjunction are isomorphisms (Mathlib), so `baseChangeΓ (N~)` is an
   isomorphism by cancelling the outer isomorphisms.
3. For general `M`, apply step 2 to `N = Γ(M)` and the naturality square of
   step 1 for `M.fromTildeΓ : Γ(M)~ ⟶ M`. Since `M.fromTildeΓ` is an
   isomorphism, so are its images under the functors involved, and
   `baseChangeΓ M` is an isomorphism.
