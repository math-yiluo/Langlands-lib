# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 4 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - FLT `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian"`: namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian` dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 227, line 238 here): `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)` is replaced by `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`. The constant `Ideal.bot_prime` no longer exists in the project's Mathlib; `Ideal.isPrime_bot` (Mathlib `RingTheory/Ideal/Prime.lean`) states the same fact, that `⊥` is a prime ideal of a nontrivial ring without zero divisors.
- No other change: the declarations and statements are the FLT ones, and the proofs are the FLT text except for the edits above.

## Content

Proof (namespace `GoodReductionJacobian.RelativeGroupLaw.DESC`). Section `Setup`: let `Z` be the
open subset of `W` of pairs whose second coordinate lies in `V`, with first projection
`p : Z ⟶ T`, and `r = d · (v ∘ second projection) : Z ⟶ A`. Section `Main`: `p` is smooth and
surjective (every point of `T` can be paired with a point of `V` in a neighbourhood of the
diagonal; `pZ_surjective` uses the hypotheses on `V`), and `r` is constant on the fibres of `p` (it
recovers `v`). Since smooth surjections are fppf coverings and representable functors are fppf
sheaves (`Scheme.fppfTopology`), `r` descends to `φ : T ⟶ A`; on `V` it equals `v` by restricting
along the diagonal.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.Zop`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.Zop_le_W`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.Zop_le_snd`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.pZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.pZ_def`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.aZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.aZ_ι`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.cZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.cZ_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.aZ_fst`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.aZ_snd`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.tZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.tZ_eq`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.dZ`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.vZ`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.rZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.rZ_base`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.comp_rZ_eq_of_fst`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.pZ_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.pZ_surjective`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.isReduced_kernelPair`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.dense_kernelPair_fstV`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC.main`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing` (same contribution).
Other imports: `Mathlib`.
