# A section of an invertible sheaf that is a frame after pullback is a frame near the image point

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback` proves the theorem `AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback`.

## Statement

Let `p : X' ⟶ X` be a morphism of schemes, `M` an invertible sheaf of modules
on `X` (the port's `Scheme.Modules.IsInvertible`), `m` a global section of
`M` and `z` a point of `X'`. Let `m'` be the image of `m` in the global
sections of `p^* M` under the unit of
`Scheme.Modules.pullbackPushforwardAdjunction p`. Call a global section `s` a
frame on an open `U` if for every open `V ≤ U` the map `g ↦ g • s|V` from
functions on `V` to sections over `V` is bijective. If `m'` is a frame on some
open neighbourhood of `z`, then `m` is a frame on some open neighbourhood of
`p z`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback`, which has the same statement. The Markdown of that module outlines the argument.
