# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 5 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian`: namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian` dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense`. Statement. `GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension_of_dense`: let `A` be a
separated group scheme over a field `k`, `T` smooth over `k`, `V ⊆ T` a dense open and `v : V ⟶ A`. Suppose the
"difference" `(b, c) ↦ v(b) v(c)⁻¹` extends to a morphism `d` on an open `W ⊆ T ×_k T` containing the diagonal
(with `d(b, c) · v(c) = v(b)` on `V × V`). Then `v` extends to `φ : T ⟶ A`.

Proof. Section `Setup`: on the open `Z = W ∩ pr₂⁻¹(V)` define `r(a, c) = d(a, c) · v(c)` (`Zop`, `rZ`). The first
projection `p : Z ⟶ T` is smooth and surjective (`pZ_surjective`: every point of `T` is a specialization of a
point of the dense open `V`, `exists_mem_specializes_of_dense`, and the diagonal lies in `W`). On the kernel pair of
`p`, which is reduced (`isReduced_kernelPair`, smoothness) and in which the locus over `V` is dense
(`dense_kernelPair_fstV`), the two pullbacks of `r` agree on the dense locus by the cocycle property, hence agree
(`ext_of_isDominant_of_isSeparated`, `A` separated). Since representable functors are fppf sheaves, `r` descends
along the fppf cover `p` to `φ : T ⟶ A`, which restricts to `v` on `V` (`comp_rZ_eq_of_fst`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.Zop`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.Zop_le_W`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.Zop_le_snd`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.pZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.pZ_def`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.aZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.aZ_ι`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.cZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.cZ_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.aZ_fst`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.aZ_snd`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.tZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.tZ_eq`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.dZ`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.vZ`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.rZ`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.rZ_base`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.comp_rZ_eq_of_fst`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isDomain_sections_spec`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isIntegrallyClosed_sections_spec`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isReduced_of_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.exists_mem_specializes_of_dense`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.pZ_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.pZ_surjective`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.isReduced_kernelPair`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.dense_kernelPair_fstV`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC.main`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk` (same contribution).
Other imports: `Mathlib`.
