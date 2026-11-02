# `Langlands.AnthropicFLT.OverBase.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid`

Adapted by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Proof module (FLT `P2M/Sol/`): proof that the translation action is a finite locally free equivalence relation.

## Source and licence

Adapted from `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid.lean` (SHA-256
`e85a6077a897c7131e57a7220786b2a0353b4cac29e88ca06e339706c00b6468`) of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
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

In this file the substitution replaces 4 implicit ring binders, 21 occurrences of `Spec (CommRingCat.of R)`, 4 further occurrences of `R` and 57 occurrences of `GoodReductionJacobian`.

The proofs are unchanged apart from the points listed below: none of them uses that the
base is affine.

**Port conventions** (as for the Library's other FLT ports):

- an attribution header comment is added at the top of the file;
- the FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`;
- the import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped;
- the FLT import `Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction` is replaced by
  its generalized copy. The Mathlib import is unchanged;
- the FLT import `Definitions.Def_JacJ1Iface` (an FLT interface module for Jacobians) is
  dropped. The file uses nothing from it;
- 3 `p2m_open "…"` commands (an FLT command from `P2M.Util` that opens the named
  namespaces and activates their scoped extensions) are replaced by standard
  `open _root_.N₁ _root_.N₂ …` commands with the same namespaces. In the first one, the
  file-local namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid_overBase.GroupLawOverBase` is dropped: it does not exist
  at that point of the file, and standard `open` rejects unknown namespaces. The file
  compiles without it;
- 4 `p2m_export "N" "a b …"` commands (an FLT command from `P2M.Util` that adds aliases
  `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by
  `export _root_.N (a b …)` with the same names;
- 7 `p2m_reactivate "N₁ N₂ …"` commands (an FLT command from `P2M.Util` that re-activates
  the scoped extensions of the named namespaces) are replaced by
  `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces;
- nothing else changes: the declarations, statements and proofs are the FLT text after the
  substitution. It compiles with the project Mathlib without errors.

## Content

Namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid_overBase.GroupLawOverBase.RelativeGroupLaw.ActionGroupoid`, with the
hypotheses of the statement module.

- *Points.* Naturality of unit and inverse (`one_natural`, `inv_natural`), the cancellation
  identities `mul_inv_mul_cancel_left` and `mul_mul_inv_cancel_left`, `action_over`, and
  `comp_action`, which describes `φ ≫ L.action ι` on points.
- *Shear.* `shear : E ×_S J ⟶ E ×_S J`, `(e, x) ↦ (e, ι(e)·x)`, and `unshear`,
  `(e, x) ↦ (e, ι(e)⁻¹·x)` (built from `actInv`), are mutually inverse (`shear_unshear`,
  `unshear_shear`, `shearIso`). They commute with the map to `S` and satisfy
  `action_eq_shear_snd : L.action ι = shear ≫ pullback.snd`.
- *Relation.* `pt e x h` is the point `(e, x)` of `E ×_S J`, and `comp_action'` and
  `comp_action_pt` compute the action on such points. `jointly_mono`: a point `(e, x)` of `E ×_S J` is
  determined by `x` and `ι(e)·x`, because right cancellation of `x` in the group of points
  (`cancel_aux`) recovers `ι(e)`, and `ι` is a monomorphism. `rel_iff`: `x ∼ y` iff `y = ι(e)·x` for a point `e` of `E` over the
  base. `equivalence`: reflexivity uses the unit (`hE_one`), symmetry the inverse (`hE_inv`)
  and transitivity products (`hE_mul`) with associativity.
- `solution`: `s` is finite, flat and locally of finite presentation by base change of
  `ι ≫ f` (instances). The same holds for `t = shear ≫ s`, since `shear` is an isomorphism.
  The last two conclusions are `jointly_mono` and `equivalence`.

## Declarations

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid_overBase.solution`, with the auxiliary declarations listed under
Content in namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid_overBase.GroupLawOverBase.RelativeGroupLaw.ActionGroupoid`.

## Dependencies

Imports `Mathlib` and `Langlands.AnthropicFLT.OverBase.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction`.
