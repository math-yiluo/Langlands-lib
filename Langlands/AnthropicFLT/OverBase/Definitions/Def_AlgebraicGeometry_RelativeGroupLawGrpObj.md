# `Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj`

Adapted by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Definition module: relative group laws over `S` versus group objects of `Over S`.

## Source and licence

Adapted from `Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean` (SHA-256
`a6558ba495ed46ea4a28dd86f33967025e5f89b20665a14915429d4de2746757`) of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean
source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`).
The text is the FLT text, transformed as described below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. FLT
`ATTRIBUTION.md` does not list this file as containing third-party material. The Lean file
starts with a header comment recording the modification.

## Changes against the FLT file

**Generalization of the base.** FLT states these results over the affine base
`Spec (CommRingCat.of R)` of a commutative ring `R : Type u`, but it uses `R` only through
that spectrum. The following purely textual substitution turns them into results over an
arbitrary base scheme `S : Scheme.{u}`; specialising `S := Spec (CommRingCat.of R)`
gives back the FLT statements.

- each binder `{R : Type u} [CommRing R]` becomes `{S : Scheme.{u}}`, and each explicit binder
  `(R : Type u) [CommRing R]` becomes `(S : Scheme.{u})`;
- each `Spec (CommRingCat.of R)` becomes `S`;
- each remaining occurrence of the identifier `R` becomes `S`; all of them are the base
  argument of `RelativeGroupLaw R f` or `relativeGroupLawOfGrpObj R f`;
- the namespace `GoodReductionJacobian` becomes `GroupLawOverBase`, and each proof-module
  namespace `P2MW.S_<name>` becomes `P2MW.S_<name>_overBase`. The Library's existing
  Spec-`R` ports keep the FLT names, and the renaming lets the generalized declarations
  coexist with them;
- the module is placed under `Langlands/AnthropicFLT/OverBase/` with its FLT relative path.

In this file the substitution replaces 28 implicit and 1 explicit ring binders, 55 occurrences of `Spec (CommRingCat.of R)`, 29 further occurrences of `R` and 1 occurrence of `GoodReductionJacobian`.

The proofs are unchanged apart from the points listed below: none of them uses that the
base is affine.

**Port conventions** (as for the Library's other FLT ports):

- an attribution header comment is added at the top of the file;
- the FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`;
- the FLT import `Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` is replaced by its
  generalized copy `Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`;
- the final FLT declaration, `RelativeGroupLaw.mul_comm_of_isProper_of_geometricallyIntegral`
  (FLT lines 314–325), is omitted. It concerns the base `Spec (CommRingCat.of K)` of a field
  `K`, not the ring base `R`, so the substitution does not generalize it. The Library port
  over `Spec R` keeps it as
  `GoodReductionJacobian.RelativeGroupLaw.mul_comm_of_isProper_of_geometricallyIntegral`.
  Nothing here or in the proof of the quotient theorem uses it;
- in the fields `map`, `map_id` and `map_comp` of `RelativeGroupLaw.yonedaGrpObjPresheaf`, FLT
  already uses `S`, `T` and `U` as local names for objects of `(Over _)ᵒᵖ`. Their bodies do not
  mention the base, so these local names merely shadow the new base name `S`;
- the file uses no `P2M.Util` commands. Nothing else changes.

## Content

All declarations are in namespace `GroupLawOverBase`. They relate group objects of the
cartesian monoidal category `Over S` to relative group laws `RelativeGroupLaw S f`:

- `overHomEquivSchemeHomOver T f : (T ⟶ Over.mk f) ≃ SchemeHomOver T.hom f`, with
  `overHomEquivSchemeHomOver_apply_coe`, `overHomEquivSchemeHomOver_symm_apply_left`,
  `overHomEquivSchemeHomOver_mk_apply`, `overHomEquivSchemeHomOver_mk_symm_apply` and
  `overHomToSchemeHomOver_injective`.
- From a group object to a group law: `relativeGroupLawOfGrpObj S f`, for
  `[GrpObj (Over.mk f)]`, is the group law on points induced by the group structure on
  morphisms `Over.mk t ⟶ Over.mk f` (`relativeGroupLawOfGrpObj_mul`, `_one`, `_inv`).
- From a group law to a group object: `RelativeGroupLaw.yonedaGrpObjPresheaf` (the presheaf of
  groups of points on `Over S`), `RelativeGroupLaw.overMkRepresentableBy` (`Over.mk f`
  represents it) and the reducible instance-valued `RelativeGroupLaw.grpObjOverMk :
  GrpObj (Over.mk f)` (via Mathlib `GrpObj.ofRepresentableBy`). They come with
  `RelativeGroupLaw.overHomToSchemeHomOver_mul`, `_one`, `_inv`,
  `RelativeGroupLaw.overHomEquivSchemeHomOver_mul`, `_one`, `_inv` and
  `RelativeGroupLaw.grpObjOverMk_mul_eq`, `_one_eq`, `_inv_eq`.
- Round trip: `relativeGroupLawOfGrpObj_grpObjOverMk_mul`, `_one`, `_inv`.
- Commutativity: `relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj`,
  `isCommMonObj_of_relativeGroupLawOfGrpObj_comm`, `isCommMonObj_iff_relativeGroupLawOfGrpObj_comm`
  and `RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm`.

The proof module `Langlands.AbelianScheme.FiniteEtaleQuotientExistenceProof` uses
`relativeGroupLawOfGrpObj`, `relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj`,
`RelativeGroupLaw.grpObjOverMk`, `RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm`,
`RelativeGroupLaw.overHomEquivSchemeHomOver_one`, `RelativeGroupLaw.overHomEquivSchemeHomOver_mul`
and `RelativeGroupLaw.overHomToSchemeHomOver_one`.

## Declarations

Namespace `GroupLawOverBase`: defs `overHomEquivSchemeHomOver`, `relativeGroupLawOfGrpObj`,
`RelativeGroupLaw.yonedaGrpObjPresheaf`, `RelativeGroupLaw.overMkRepresentableBy`,
`RelativeGroupLaw.grpObjOverMk`; all other names listed under Content are theorems.

## Dependencies

Imports `Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`.
