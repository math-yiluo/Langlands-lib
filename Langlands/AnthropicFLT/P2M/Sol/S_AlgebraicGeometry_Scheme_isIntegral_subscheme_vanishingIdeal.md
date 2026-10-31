# The reduced closed subscheme on an irreducible closed subset is integral

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.solution`. Its statement is that of `AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal` states under its FLT name.

## Statement

Let `V` be a scheme and `Z` a closed subset of `V` that is irreducible. Let
`Scheme.IdealSheafData.vanishingIdeal Z` be Mathlib's ideal sheaf of `V`
vanishing on `Z`, so that its `subscheme` is the reduced closed subscheme
structure on `Z`. Then this subscheme is integral (`IsIntegral`).

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

A scheme is integral when its underlying space is irreducible and it is
reduced (`isIntegral_of_irreducibleSpace_of_isReduced`).

- The underlying space of the subscheme is the support of the ideal sheaf,
  which is `Z` (`IdealSheafData.coe_support_vanishingIdeal`); a subspace that
  is an irreducible set is an irreducible space (`Subtype.irreducibleSpace`).
- Reducedness is checked on the affine open cover `subschemeCover` of the
  subscheme (`IsReduced.of_openCover`). Over an affine open `U` of `V` the
  chart is `Spec` of `Γ(V, U)` modulo the ideal of the vanishing ideal sheaf
  on `U`, which is the vanishing ideal of a subset of the prime spectrum
  (`IdealSheafData.vanishingIdeal_ideal`), hence a radical ideal
  (`PrimeSpectrum.isRadical_vanishingIdeal`). The quotient by a radical ideal
  is reduced, and an affine scheme is reduced exactly when its ring is
  (`affine_isReduced_iff`).
