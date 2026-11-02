# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - FLT `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry TopologicalSpace Opposite"`: namespace `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry` dropped.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `AlgebraicGeometry.HartogsAffine`).

- `Affine`: for an affine scheme `X`, points correspond to primes of `Γ(X, ⊤)` (`pointOfPrime`),
  stalks are localizations, and `Γ(X, ⊤)` is integrally closed when the stalks are.
- `Sections`: for an integral affine locally noetherian `X` with integrally closed stalks and an open
  `V` containing all points with stalk of dimension `≤ 1`, restriction of sections from `X` to `V`
  is bijective (`restrict_injective`, `restrict_surjective`, `appTop_bijective`; surjectivity uses
  `IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one`), so morphisms from `V` to an
  affine scheme extend uniquely (`existsUnique_extension`).
- `LocallyIntegral`, `Wrapper`: every point has an integral affine open neighbourhood
  (`exists_isDomain_away`, `exists_isIntegral_affineOpen`).
- `Glue`, `Main`: the hypotheses restrict to opens (`hyp_restrict`); on each integral affine open
  there is a unique extension (`exists_piece`); morphisms from an integral scheme to an affine
  scheme that agree on a nonempty open are equal (`ext_of_agree`); the pieces glue (`hartogs`).
  `solution` applies `hartogs`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.pointOfPrime`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.primeIdealOf_pointOfPrime`
- scoped instance `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.isLocalization_stalk_pointOfPrime`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.ringKrullDim_stalk_pointOfPrime`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.isIntegrallyClosed_sections`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.genericPoint_mem_of_ringKrullDim`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.restrict_injective`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.restrict_surjective`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.appTop_bijective`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.existsUnique_extension`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.exists_isDomain_away`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.exists_isIntegral_affineOpen`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.hyp_restrict`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.exists_piece`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.ext_of_agree`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.AlgebraicGeometry.HartogsAffine.hartogs`
- theorem `P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one` (same contribution).
Other imports: `Mathlib`.
