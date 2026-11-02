# `Langlands.AnthropicFLT.OverBase.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction`

Adapted by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Definition module: the translation action of a subscheme on a scheme with a relative group law.

## Source and licence

Adapted from `Definitions/Def_GoodReductionJacobian_RelativeGroupLawAction.lean` (SHA-256
`cd431bc11c824f4ee70f81c456ecb5871a3c6ca868d6f71091cdcfb622777a11`) of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
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

In this file the substitution replaces 1 implicit ring binder, 3 occurrences of `Spec (CommRingCat.of R)`, 7 further occurrences of `R` and 2 occurrences of `GoodReductionJacobian`.

The proofs are unchanged apart from the points listed below: none of them uses that the
base is affine.

**Port conventions** (as for the Library's other FLT ports):

- an attribution header comment is added at the top of the file;
- the FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`;
- the FLT import `Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` is replaced by its
  generalized copy `Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`. The Mathlib
  import is unchanged;
- the file uses no `P2M.Util` commands. Nothing else changes.

## Content

Namespace `GroupLawOverBase.RelativeGroupLaw`. Let `f : J ⟶ S`, `L : RelativeGroupLaw S f`
and `ι : E ⟶ J`. The scheme `pullback (ι ≫ f) f` is `E ×_S J`.

- `actionSource f ι : pullback (ι ≫ f) f ⟶ S` is `pullback.snd ≫ f`.
- `actionFstPoint L ι` and `actionSndPoint L ι` are the two `E ×_S J`-points of `J`,
  `pullback.fst ≫ ι` and `pullback.snd` (`actionFstPoint_coe`, `actionSndPoint_coe`).
- `action L ι : pullback (ι ≫ f) f ⟶ J` is their product under `L`. On points it is
  `(e, x) ↦ ι(e) · x` (`action_def`), and it lies over `S` (`action_over`).

## Declarations

- abbrev `GroupLawOverBase.RelativeGroupLaw.actionSource`
- defs `GroupLawOverBase.RelativeGroupLaw.actionFstPoint`, `…actionSndPoint`, `…action`
- theorems `GroupLawOverBase.RelativeGroupLaw.action_def`, `…actionFstPoint_coe`,
  `…actionSndPoint_coe`, `…action_over`

## Dependencies

Imports `Mathlib` and `Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`.
