# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated`

Ported module of the proof submitted by task `e36ae7da-512e-4a4d-a902-71146c92ec82` (descent of properness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `SolCH`). `HasEnvelope f S` says that some `X' → X` as in the statement, with `π` proper,
has image exactly `S`. It holds for `S = ∅`, is stable under finite unions (disjoint unions `X₁ ⨿ X₂`,
`P₁ ⨿ P₂` with `coprod.desc`/`coprod.map`, which preserve properness and open immersions), and holds for
the image of a closed immersion from an integral scheme by the integral case (applied to the composite
`Z → X → Spec A`). Each irreducible component of `X`, with its reduced induced structure
(`Scheme.IdealSheafData.vanishingIdeal`, `isIntegral_subscheme_vanishingIdeal`), is such an integral closed
subscheme. `X` is a noetherian scheme (locally of finite type over a noetherian ring, quasi-compact), so it
has finitely many irreducible components, and their union is `X`; the envelope of the union gives a
surjective `π`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.coprodMap_of`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.isOpenImmersion_coprodMap`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.isProper_coprodMap`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.isProper_coprodDesc`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.range_coprodDesc`
- def `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.HasEnvelope`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.HasEnvelope.empty`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.HasEnvelope.union`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.HasEnvelope.of_isIntegral`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.isReduced_subscheme_vanishingIdeal`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.isIntegral_subscheme_vanishingIdeal`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.hasEnvelope_of_mem_irreducibleComponents`
- lemma `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.hasEnvelope_biUnion`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH.main`
- theorem `P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral` (ported by this task).
All modules also import `Mathlib`.
