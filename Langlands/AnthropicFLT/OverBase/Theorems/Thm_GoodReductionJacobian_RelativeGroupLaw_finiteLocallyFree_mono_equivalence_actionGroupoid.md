# `Langlands.AnthropicFLT.OverBase.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid`

Adapted by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Statement module (FLT `Theorems/`): the translation action of a finite locally free subgroup is a finite locally free equivalence relation.

## Source and licence

Adapted from `Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid.lean` (SHA-256
`27facf8f0db1c70d6602dd10874e22976b7fb64cf2337ce68ea8fbfe764fa1a5`) of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
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

In this file the substitution replaces 1 implicit ring binder, 4 occurrences of `Spec (CommRingCat.of R)`, 1 further occurrence of `R` and 2 occurrences of `GoodReductionJacobian`.

The proofs are unchanged apart from the points listed below: none of them uses that the
base is affine.

**Port conventions** (as for the Library's other FLT ports):

- an attribution header comment is added at the top of the file;
- the FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`;
- the import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped;
- the FLT import `Definitions.Def_JacJ1Iface` (an FLT interface module for Jacobians) is
  dropped. The file uses nothing from it;
- the FLT imports `Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction` and
  `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid` are replaced by their generalized copies under
  `Langlands.AnthropicFLT.OverBase`. The Mathlib import is unchanged;
- the FLT proof `by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid.solution` (a tactic from
  `P2M.Util`) is replaced by the term `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid_overBase.solution L ι hE_one hE_mul hE_inv`, the companion
  solution theorem applied to the explicit arguments of the theorem. Nothing else changes.

## Content

`GroupLawOverBase.RelativeGroupLaw.finiteLocallyFree_mono_equivalence_actionGroupoid`.
Let `f : J ⟶ S` carry a relative group law `L : RelativeGroupLaw S f`. Let `ι : E ⟶ J` be a
closed immersion with `ι ≫ f` finite, flat and locally of finite presentation, and suppose
`E` is stable under the group law on points: unit (`hE_one`), products (`hE_mul`) and
inverses (`hE_inv`) of points factoring through `ι` again factor through `ι`. Write
`s = pullback.snd (ι ≫ f) f` and `t = L.action ι`, the two maps `E ×_S J ⟶ J`
(`(e, x) ↦ x` and `(e, x) ↦ ι(e) · x`).
Then:

- `s` and `t` are finite, flat and locally of finite presentation;
- `s` and `t` are jointly monomorphic: two maps `a b : T ⟶ E ×_S J` with `a ≫ s = b ≫ s` and
  `a ≫ t = b ≫ t` are equal;
- for every scheme `T`, the relation "there is `φ : T ⟶ E ×_S J` with `φ ≫ s = x` and
  `φ ≫ t = y`" on morphisms `x y : T ⟶ J` is an equivalence relation.

The proof term applies the companion solution theorem.

## Declarations

- theorem `GroupLawOverBase.RelativeGroupLaw.finiteLocallyFree_mono_equivalence_actionGroupoid`

## Dependencies

Imports `Mathlib`, `Langlands.AnthropicFLT.OverBase.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction` and
`Langlands.AnthropicFLT.OverBase.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid`.
