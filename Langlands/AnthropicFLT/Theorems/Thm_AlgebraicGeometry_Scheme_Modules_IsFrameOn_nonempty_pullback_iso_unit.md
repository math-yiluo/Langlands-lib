# A frame trivializes a module on every smaller open

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit` proves the theorem `AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit`.

## Statement

Let `X` be a scheme, `M` a sheaf of modules on `X`, `U` and `V` opens of `X`
and `s` a section of `M` over `U`. Suppose `s` is a frame on `V`
(`Scheme.Modules.IsFrameOn s V`, from the FLT module
`Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`): for every open
`W ≤ U ⊓ V`, the map `Γ(X, W) → Γ(M, W)`, `g ↦ g • s|W`, is bijective. Then
for every open `W` with `W ≤ U` and `W ≤ V`, the pullback of `M` along the
open immersion `W.ι` is isomorphic to the structure sheaf
`SheafOfModules.unit` of the open subscheme `W`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit`, which has the same statement. The Markdown of that module outlines the argument.
