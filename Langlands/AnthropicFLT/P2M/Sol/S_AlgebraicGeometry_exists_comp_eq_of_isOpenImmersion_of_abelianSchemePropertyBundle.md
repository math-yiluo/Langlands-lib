# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 4 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry _root_.NeronModelInfra _root_.GoodReductionJacobian`: namespace `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry` dropped.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 50, line 61 here): `(tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 3 1` is replaced by `(tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 4 2`. In the project's Mathlib, `List.TFAE.out` takes 1-indexed positions (FLT's Mathlib used 0-indexed ones); the list of `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` is unchanged, so both indices are increased by one and the proved equivalence is the same.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle`. Statement. `AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle` (Weil extension over a
field): let `X ⟶ Spec k` be smooth, separated, quasi-compact with `X` irreducible, `A ⟶ Spec k` satisfy the
abelian scheme property bundle, and `φ : U ⟶ A` a morphism over `k` from a nonempty open subscheme `U ⊆ X`.
Then `φ` extends to a morphism `ψ : X ⟶ A` over `k`.

Proof. The stalks of `X` are integrally closed domains (ported `Smooth.isDomain_and_isIntegrallyClosed_stalk`).
By the ported `RelativeGroupLaw.exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one`,
the "difference" map `(x, y) ↦ φ(x) φ(y)⁻¹` extends over an open containing all points of codimension
`≤ 1` of the diagonal (using that rational maps to the proper `A` are defined at points with valuation-ring
stalks, ported `Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk`); then
`RelativeGroupLaw.exists_extension_of_diagonal_difference_extension_of_dense` extends `φ` to all of `X`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- scoped instance `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField.EXT.isDomain_sections_spec`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField.EXT.isIntegrallyClosed_sections_spec`
- theorem `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField.EXT.isReduced_of_smooth`
- theorem `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField.EXT.valuationRing_stalk_of_ringKrullDim_le_one`
- theorem `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.AlgebraicGeometry.WeilExtField.EXT.main`
- theorem `P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk` (same contribution).
Other imports: `Mathlib`.
