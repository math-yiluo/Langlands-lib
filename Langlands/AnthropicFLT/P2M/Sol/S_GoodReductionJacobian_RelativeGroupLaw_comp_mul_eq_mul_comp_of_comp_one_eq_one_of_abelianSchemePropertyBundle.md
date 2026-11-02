# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle`. Statement. `GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle`: over a
field `k`, let `G` be a separated, quasi-compact, smooth, connected group scheme and `A` an abelian variety (the
property bundle). A morphism `φ : G ⟶ A` over `k` sending the unit to the unit is a homomorphism.

Proof. Sections `Defect`, `DefectField`: the defect `δ(x, y) = φ(xy)(φ(x)φ(y))⁻¹` is natural; `φ` is a homomorphism at
`(x, y)` (`IsHomAt`) iff `δ(x, y) = 1`, and `δ(1, y) = δ(x, 1) = 1`. By the ported
`SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat` (`G ×_k G` is reduced, being smooth) it is
enough to check `IsHomAt` at the points over an algebraic closure `K` (`isHomAt_universal`). Section `GoodSet`:
let the good set be the `K`-points `g` of `G_K` with `δ(g, -) = 1`. It contains the unit and is stable along smooth
proper curves (`goodSet_stable`): for `ψ : U ⟶ G_K` from an open of a smooth proper curve `C`, the map
`(c, x) ↦ δ(ψ c, x)` extends from `U` to `C` (ported `exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle`,
section `OpenPiece`), and by the ported rigidity lemma `exists_eq_snd_comp_of_comp_eq_const_of_isProper`
(`δ(c, 1) = 1` is constant) it does not depend on `c`. Section `Geometry`: `G_K` is integral (ported
`RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`,
`Smooth.isDomain_and_isIntegrallyClosed_stalk`). The ported `mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem`
shows that every `K`-point is good (`isHomAt_point`), which concludes.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.inv_natural`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.comp_schemeHomOverComp`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.IsHomAt`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.defect`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.defect_natural`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.defect_natural_val`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.defect_eq_one_iff`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isHomAt_natural`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isHomAt_one_left`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isHomAt_one_right`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isDomain_sections_spec`
- scoped instance `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isIntegrallyClosed_sections_spec`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isReduced_of_smooth`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.geometricallyIrreducible_of_connectedSpace`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.irreducibleSpace_pullback`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isIntegral_pullback`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.range_subset_range_ι`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.liftW`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.liftW_ι`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.liftW_res`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.piPt`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.cstPt`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.goodSet`
- def `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.unitPt`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.unitPt_snd`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.unitPt_fst`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.unitPt_mem_goodSet`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.goodSet_stable`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.mem_goodSet`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isHomAt_point`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.isHomAt_universal`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.P2mRigNP.main`
- theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension` (Library), `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem` (same contribution).
Other imports: `Mathlib`.
