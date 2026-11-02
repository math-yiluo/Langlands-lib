# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 5 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian`: namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian` dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense`. Statement. `GoodReductionJacobian.RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense`: let `A` be a separated
group scheme over a field `k`, `T` smooth over `k`, `V ⊆ T` dense open and `v : V ⟶ A`. There is a greatest open
`W ⊆ T ×_k T` containing `V × V` with a morphism `d` on `W` extending the difference `(b, c) ↦ v(b) v(c)⁻¹`: every
other open `W'` with a morphism agreeing with `d` on an open dense in `W'` is contained in `W`, and the morphisms
agree.

Proof. `T ×_k T` is smooth, hence reduced (local `isReduced_of_smooth`, `isReduced_pullback`), and `A` is separated
(`isSeparated_of_isSeparated_over`), so two morphisms to `A` that agree on a dense open of a common domain agree on
the whole intersection (`eq_on_inf_of_eq_on_dense`). Let `W` be the union of all opens carrying an extension of the
difference map defined on `V × V` (`prodOpen`, dense by `dense_prodOpen`; `diffMap`); the extensions agree on
overlaps and glue (`exists_glue_of_eq_on_dense`, sections `Main`, `Main2`). Maximality follows from the same
agreement argument (`recovery_core`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.isDomain_sections_spec`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.isIntegrallyClosed_sections_spec`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.isReduced_of_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.eq_on_inf_of_eq_on_dense`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.pullback_fst_comp_eq_of_eq_on_inf`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.exists_glue_of_eq_on_dense`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.inv_natural`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.prodOpen`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.mem_prodOpen_iff`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.prFst`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.prSnd`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.bD_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.cD_ι`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.pt₁`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.pt₂`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.diffMap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.recovery_core`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.dense_prodOpen`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.isReduced_pullback`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.isSeparated_of_isSeparated_over`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.mem_opens_of_base`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM.main`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk` (same contribution).
Other imports: `Mathlib`.
