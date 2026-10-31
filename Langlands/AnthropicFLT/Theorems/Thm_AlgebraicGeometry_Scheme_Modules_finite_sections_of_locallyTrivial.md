# Sections of a locally trivial module over an affine open are finitely generated

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial` proves the theorem `AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial`.

## Statement

Let `X` be a scheme and `M` a sheaf of modules on `X` that is locally
trivial: every point has an open neighbourhood `V` such that the pullback of
`M` along `V.ι` is isomorphic to the structure sheaf of `V`. Then for every
affine open `U` of `X`, the module of sections `Γ(M, U)` is finitely
generated over the ring `Γ(X, U)`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial`, which has the same statement. The Markdown of that module outlines the argument.
