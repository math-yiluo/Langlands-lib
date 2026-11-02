# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 26 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 12 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian`: namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian` dropped.
- 16 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 141, line 152 here): `(IsLocalRing.local_hom_TFAE φ).out 0 3` is replaced by `(IsLocalRing.local_hom_TFAE φ).out 1 4`. In the project's Mathlib, `List.TFAE.out` takes 1-indexed positions (FLT's Mathlib used 0-indexed ones); the list of `IsLocalRing.local_hom_TFAE` is unchanged, so both indices are increased by one and the proved implication is the same.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one`. Statement. `GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one`: let `A`
be a separated group scheme over a field `k`, `T` smooth over `k`, `V ⊆ T` an open containing every point whose
local ring has dimension `≤ 1`, and `v : V ⟶ A`. Then the difference `(b, c) ↦ v(b) v(c)⁻¹` extends to an open
`W ⊆ T ×_k T` containing the diagonal.

Proof (Weil's extension argument). `V` is dense (`dense_of_forall_ringKrullDim_le_one`). Take the greatest extension
`(W, d)` of the ported `RelativeGroupLaw.exists_isGreatest_opens_difference_extension_of_dense`. The difference is
the unit on the diagonal of `V` (`diagonal_restrict_comp_eq_unit`, `eq_one_of_mul_eq`). If the diagonal point of
`x` were outside `W`, the ported `Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain`
(applied on an affine integral normal component, `exists_rationalMap_component_affine`; stalks of smooth schemes
are normal domains, ported `Smooth.isDomain_and_isIntegrallyClosed_stalk`, `isOpen_irreducibleComponent_of_isDomain_stalk`)
gives a point of `T ×_k T` of codimension `≤ 1` outside `W` specializing to it. Dimension theory of the regular
local rings of `T ×_k T` (ported `Smooth.isRegularLocalRing_stalk`, `IsRegularLocalRing.spanFinrank_ker_add_ringKrullDim_eq`,
`IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height`, `IsRegularLocalRing.depth_self_eq_ringKrullDim`;
local `exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height`, `krull_transfer_inputs`,
`diag_assembly`) shows that such a point near the diagonal projects to points of codimension `≤ 1` of `T`, hence lies
over `V × V ⊆ W`, a contradiction.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.exists_nat_of_add_natCast_eq`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.exists_nat_ringKrullDim_of_le`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.height_add_le_of_strictChain`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.exists_isPrime_map_le_height_le_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.coheight_fromSpecStalk`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.ringKrullDim_stalk_fromSpecStalk`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.isDomain_sections_spec`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.isIntegrallyClosed_sections_spec`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.isDomain_and_isIntegrallyClosed_stalk_of_field`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.isReduced_of_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.exists_specializes_ringKrullDim_stalk_le_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.dense_of_forall_ringKrullDim_le_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.dense_inf_preimage_of_dense`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3.eq_one_of_mul_eq`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3.isDominant_homOfLE_inf`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3.diagonal_restrict_comp_eq_unit`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3b.exists_rationalMap_component_affine`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.exists_nat_ringKrullDim_eq_of_isRegularLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.isCohenMacaulayOfDim_of_isRegularLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.ringKrullDim_quotient_add_height_of_isRegularLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.krull_transfer_inputs`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.isIntegral_and_isLocallyNoetherian_and_isIntegrallyClosed_of_isIrreducible`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.exists_isAffineOpen_forall_mem_of_isLocalRing`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.specializes_ι_of_specializes`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.specializes_of_specializes_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.ringKrullDim_stalk_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B.ι_base_apply_mk`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.diag_assembly`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library), `Langlands.AnthropicFLT.Definitions.Def_Patching_CohenMacaulayOfDim` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_spanFinrank_ker_add_ringKrullDim_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_depth_self_eq_ringKrullDim` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain` (same contribution).
Other imports: `Mathlib`.
