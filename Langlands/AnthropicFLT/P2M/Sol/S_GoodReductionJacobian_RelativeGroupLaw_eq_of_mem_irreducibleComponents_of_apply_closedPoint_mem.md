# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem`. Statement. `GoodReductionJacobian.RelativeGroupLaw.eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem`: in a group scheme
locally of finite type over an algebraically closed field `k`, a `k`-point lies on only one irreducible
component.

Proof. Section `Maps`: translations by `k`-points are automorphisms over `k` (`transl`), so they permute the irreducible
components (`image_mem_irreducibleComponents`); translating, it suffices to treat components through the unit
(`eq_of_clpt_mem`). Section `Component`: give the components their reduced subscheme structures (`redSub`, via the
ported `Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker`); they are integral and of finite type
over `k`, hence geometrically integral (ported `geometricallyIntegral_of_isAlgClosed`), so `Z × Z'` is irreducible.
Section `Identity`: the image of multiplication `Z × Z' ⟶ N` is irreducible (`isIrreducible_range_mulMap`) and
contains `Z` and `Z'` (`subset_range_mulMap_left/right`, using the unit); by maximality `Z = Z'`
(`eq_of_one_mem`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.const`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.const_coe`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.const_pt`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.const_transition`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.const_mul`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.const_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.inv_natural`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.const_inv`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.transl`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.transl_over`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.comp_transl`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.transl_point`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.transl_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.transl_comp`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.isIso_transl`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.clpt`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.transl_clpt`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.transl_clpt_one`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.image_mem_irreducibleComponents`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.eq_of_mem_irreducibleComponents_of_subset`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.redSub`
- abbrev `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.redι`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.isReduced_redSub`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.range_redι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.redι_apply_mem`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.redLift`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.redLift_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.irreducibleSpace_redSub`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.isIntegral_redSub`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.ratLift`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.ratLift_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.ratLift_over`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.mulMap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.lift_mulMap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.subset_range_mulMap_left`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.subset_range_mulMap_right`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.isIrreducible_range_mulMap`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.eq_of_one_mem`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.P2mGroupSchemeComponents.eq_of_clpt_mem`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker` (same contribution).
Other imports: `Mathlib`.
