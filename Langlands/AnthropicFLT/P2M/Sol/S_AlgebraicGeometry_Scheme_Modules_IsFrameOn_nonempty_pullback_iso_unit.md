# A frame trivializes a module on every smaller open

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

1. Restriction of modules to `W` is written as the pushforward of sheaves of
   modules along the identity of the structure sheaf of `W`
   (`restrictFunctor'`). It equals Mathlib's `Scheme.Modules.restrictFunctor W.ι`
   (the comparison reduces to `Scheme.Opens.ι_appIso`), and so is isomorphic
   to the pullback along `W.ι` (`Scheme.Modules.restrictFunctorIsoPullback`).
2. Let `τ = s|W`. Multiplication by `τ` defines a morphism of sheaves of
   modules `smulSectionHom` from the structure sheaf of `W` to the
   restriction of `M`: on an open `W'` of `W`, with image `W.ι(W')` in `X`, it
   sends `a` to `a • τ|W.ι(W')`. Naturality follows from
   `Scheme.Modules.map_smul`.
3. Each component of this morphism is bijective, by the frame hypothesis
   applied to `W.ι(W') ≤ W ≤ U ⊓ V` (after rewriting the double restriction of
   `s` as one restriction). A morphism of sheaves of modules whose components
   are bijective is an isomorphism: bijective maps of abelian groups are
   isomorphisms, isomorphisms of presheaves are checked objectwise, and the
   forgetful functors from sheaves of modules to presheaves of modules and to
   presheaves of abelian groups reflect isomorphisms.

Composing the inverse of this isomorphism with the comparison of step 1 gives
the required isomorphism.
