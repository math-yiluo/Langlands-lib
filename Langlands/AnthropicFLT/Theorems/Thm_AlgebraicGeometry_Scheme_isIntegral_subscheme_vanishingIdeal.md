# The reduced closed subscheme on an irreducible closed subset is integral

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal` proves the theorem `AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal`.

## Statement

Let `V` be a scheme and `Z` a closed subset of `V` that is irreducible. Let
`Scheme.IdealSheafData.vanishingIdeal Z` be Mathlib's ideal sheaf of `V`
vanishing on `Z`, so that its `subscheme` is the reduced closed subscheme
structure on `Z`. Then this subscheme is integral (`IsIntegral`).

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal`, which has the same statement. The Markdown of that module outlines the argument.
