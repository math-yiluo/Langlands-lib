# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - FLT `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.AlgebraicGeometry"`: namespace `P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.AlgebraicGeometry` dropped.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `AlgebraicGeometry.SmoothRegularDVR`). `isRegularRing_mvPolynomial_fin`: polynomial
rings in finitely many variables over the discrete valuation ring `R` are regular.
`isRegularLocalRing_of_isLocalization_atPrime`: localizations of smooth `R`-algebras at primes are
regular, by writing the algebra locally as étale over such a polynomial ring and applying
`isRegularLocalRing_localization_atPrime_of_etale_of_comap`. `solution`: choose an affine open on
which `t` is standard smooth and apply this to the stalk.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.AlgebraicGeometry.SmoothRegularDVR.isRegularRing_mvPolynomial_fin`
- theorem `P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.AlgebraicGeometry.SmoothRegularDVR.isRegularLocalRing_of_isLocalization_atPrime`
- theorem `P2MW.S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent` (same contribution).
Other imports: `Mathlib`.
