# The tensor product of two invertible sheaves is invertible

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2` states under its FLT name.

## Statement

Let `X` be a scheme and `L`, `M` sheaves of modules on `X` that are
invertible in the sense of the port's `Scheme.Modules.IsInvertible`: every
point has an open neighbourhood `U` such that the pullback along the
inclusion `U.ι` is isomorphic to the structure sheaf of `U`. Then the tensor
product `L ⊗ M`, for the monoidal structure on sheaves of modules of the
port (`Definitions/Def_SheafOfModules_MonoidalV2`), is invertible.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

The module first defines `trivializationOfLE`: a trivialization of `L` over
an open `U` restricts to a trivialization over any open `V ≤ U`. It is the
composite of the isomorphisms `pullbackCongr` (for `V.ι = homOfLE ≫ U.ι`),
`pullbackComp`, the pullback of the given trivialization along the inclusion
`V ⟶ U`, and `pullbackUnitIso` (the pullback of the structure sheaf is the
structure sheaf).

Given `x`, choose trivializations of `L` on `U ∋ x` and of `M` on `U' ∋ x`.
On `U ⊓ U'` the pullback of `L ⊗ M` is the tensor product of the pullbacks
(`pullbackTensorObjIso`), which by the restricted trivializations is
isomorphic to `𝟙 ⊗ 𝟙`, and the left unitor identifies this with the
structure sheaf.
