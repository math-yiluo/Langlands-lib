# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj`

## Source

Port of `Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- The import of the FLT module `Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (the file has no other import).
- The FLT lakefile options are inserted after the import: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- No other change: the declarations, statements and proofs are the FLT text.

## Contents

Declarations, with their original FLT names, all in namespace `GoodReductionJacobian` (no new definitions or
statements are introduced). The file relates group objects of `Over (Spec R)` to FLT's `RelativeGroupLaw R f`
(group laws on the points `SchemeHomOver t f`, natural in `t`):

- `overHomEquivSchemeHomOver T f : (T ⟶ Over.mk f) ≃ SchemeHomOver T.hom f` with theorems
  `overHomEquivSchemeHomOver_apply_coe`, `overHomEquivSchemeHomOver_symm_apply_left`,
  `overHomEquivSchemeHomOver_mk_apply`, `overHomEquivSchemeHomOver_mk_symm_apply`, `overHomToSchemeHomOver_injective`.
- From a group object to a group law: def `relativeGroupLawOfGrpObj R f` (for `[GrpObj (Over.mk f)]`, the group law
  on points induced by the group structure on morphisms `Over.mk t ⟶ Over.mk f`), with theorems
  `relativeGroupLawOfGrpObj_mul`, `relativeGroupLawOfGrpObj_one`, `relativeGroupLawOfGrpObj_inv`.
- From a group law to a group object: defs `RelativeGroupLaw.yonedaGrpObjPresheaf` (the presheaf of groups of points),
  `RelativeGroupLaw.overMkRepresentableBy` (it is represented by `Over.mk f`) and the reducible
  `RelativeGroupLaw.grpObjOverMk : GrpObj (Over.mk f)` (via Mathlib `GrpObj.ofRepresentableBy`), with theorems
  `RelativeGroupLaw.overHomToSchemeHomOver_mul`, `RelativeGroupLaw.overHomToSchemeHomOver_one`,
  `RelativeGroupLaw.overHomToSchemeHomOver_inv`, `RelativeGroupLaw.overHomEquivSchemeHomOver_mul`,
  `RelativeGroupLaw.overHomEquivSchemeHomOver_one`, `RelativeGroupLaw.overHomEquivSchemeHomOver_inv`,
  `RelativeGroupLaw.grpObjOverMk_mul_eq`, `RelativeGroupLaw.grpObjOverMk_one_eq`, `RelativeGroupLaw.grpObjOverMk_inv_eq`.
- Round trip: theorems `relativeGroupLawOfGrpObj_grpObjOverMk_mul`, `relativeGroupLawOfGrpObj_grpObjOverMk_one`,
  `relativeGroupLawOfGrpObj_grpObjOverMk_inv`.
- Commutativity: theorems `relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj`,
  `isCommMonObj_of_relativeGroupLawOfGrpObj_comm`, `isCommMonObj_iff_relativeGroupLawOfGrpObj_comm`,
  `RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm`, `RelativeGroupLaw.mul_comm_of_isProper_of_geometricallyIntegral`.

The bridge `Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof` uses `relativeGroupLawOfGrpObj`,
`relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj`, `RelativeGroupLaw.grpObjOverMk`,
`RelativeGroupLaw.overHomToSchemeHomOver_mul` and `RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm`.

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (part of
the Library's port for the noetherian line-bundle seesaw).
