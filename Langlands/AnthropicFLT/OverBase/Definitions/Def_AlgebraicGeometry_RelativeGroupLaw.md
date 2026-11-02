# `Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`

Adapted by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Definition module: group laws on the points of a scheme over an arbitrary base scheme `S`.

## Source and licence

Adapted from `Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean` (SHA-256
`983cdb408d5599de74629f79292e5e046be3d6aea1f1e55b6b1a8fc1d7234d1b`) of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
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

In this file the substitution replaces 6 implicit and 2 explicit ring binders, 26 occurrences of `Spec (CommRingCat.of R)`, 7 further occurrences of `R` and 2 occurrences of `GoodReductionJacobian`.

The proofs are unchanged apart from the points listed below: none of them uses that the
base is affine.

**Port conventions** (as for the Library's other FLT ports):

- an attribution header comment is added at the top of the file;
- the FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`;
- the FLT import `Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` is
  replaced by the Library module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`.
  That module is the Library's port of this same FLT file over `Spec R`, and it imports the
  Library port of the carrier module, which provides `SchemeHomOver`;
- FLT lines 14–64, the block `namespace NeronModelInfra … end NeronModelInfra`, are omitted.
  It declares `schemeHomOverToOverHom`, `schemeHomOverToOverHom_left`, `overHomToSchemeHomOver`,
  `overHomToSchemeHomOver_coe`, `overHomToSchemeHomOver_schemeHomOverToOverHom`,
  `schemeHomOverToOverHom_overHomToSchemeHomOver`, `schemeHomOverEquivOverHom`,
  `schemeHomOverEquivOverHom_apply` and `schemeHomOverEquivOverHom_symm_apply`. These
  declarations are already stated over an arbitrary base `B`. The imported Library port
  declares them with byte-identical text, so declaring them again would be a duplicate
  declaration. This file uses the imported ones;
- the file uses no `P2M.Util` commands. Nothing else changes.

## Content

All declarations are in namespace `GroupLawOverBase`. Schemes live in a fixed universe `u`.
`SchemeHomOver t f`, for `t : T ⟶ S` and `f : A ⟶ S`, is the type of morphisms `T ⟶ A` over
`S` (the `T`-points of `A`).

- `schemeHomOverComp ψ hψ x`: for `ψ : T' ⟶ T` over the base and a `T`-point `x` of `A`, the
  `T'`-point `ψ ≫ x` (`schemeHomOverComp_coe`).
- `structure RelativeGroupLaw (S : Scheme.{u}) (f : A ⟶ S)`: for every `t : T ⟶ S`, a
  multiplication `mul t`, a unit `one t` and an inverse `inv t` on `SchemeHomOver t f`,
  satisfying `mul_assoc`, `one_mul`, `mul_one` and `inv_mul_cancel`, with multiplication
  natural in `T` (`mul_natural`). By Yoneda this is a group-scheme structure on `A` over `S`,
  given on points.
- `RelativeGroupLaw.IsCommutative` (commutativity on all `T`-points) and
  `IsCommutative.mul_comm`; `RelativeGroupLaw.pointGroup t`, the `Group` structure on the
  `T`-points; `RelativeGroupLaw.mul_inv_cancel`; `RelativeGroupLaw.one_natural` (the unit is
  natural in `T`).
- `trivialRelativeGroupLaw S`: the group law on `𝟙 S`. `relativeGroupLaw_pointwise_eq_of_isIso`:
  any two group laws on an isomorphism agree.

## Declarations

- def `GroupLawOverBase.schemeHomOverComp`, theorem `GroupLawOverBase.schemeHomOverComp_coe`
- structure `GroupLawOverBase.RelativeGroupLaw`
- def `GroupLawOverBase.RelativeGroupLaw.IsCommutative`, theorem
  `GroupLawOverBase.RelativeGroupLaw.IsCommutative.mul_comm`
- def `GroupLawOverBase.RelativeGroupLaw.pointGroup`, theorems
  `GroupLawOverBase.RelativeGroupLaw.mul_inv_cancel`, `GroupLawOverBase.RelativeGroupLaw.one_natural`
- def `GroupLawOverBase.trivialRelativeGroupLaw`, theorem
  `GroupLawOverBase.relativeGroupLaw_pointwise_eq_of_isIso`

## Dependencies

Imports `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library).
