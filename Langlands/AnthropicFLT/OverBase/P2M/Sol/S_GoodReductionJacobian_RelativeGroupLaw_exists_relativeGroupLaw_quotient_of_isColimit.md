# `Langlands.AnthropicFLT.OverBase.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit`

Adapted by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Proof module (FLT `P2M/Sol/`): proof that a commutative relative group law descends to the quotient by a finite locally free subgroup.

## Source and licence

Adapted from `P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.lean` (SHA-256
`720fd28cdc49bd3893b45f759b212db0e6fa528f2145696ef2811b0dd571ccf7`) of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
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

In this file the substitution replaces 12 implicit ring binders, 63 occurrences of `Spec (CommRingCat.of R)`, 14 further occurrences of `R` and 182 occurrences of `GoodReductionJacobian`.

The proofs are unchanged apart from the points listed below: none of them uses that the
base is affine.

**Port conventions** (as for the Library's other FLT ports):

- an attribution header comment is added at the top of the file;
- the FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`;
- the import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped;
- the FLT import `Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction` is replaced by
  its generalized copy. The FLT import
  `Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`
  is replaced by the existing port
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`.
  That theorem does not mention a ring, so it needs no generalization and has no `OverBase`
  copy. The Mathlib import is unchanged;
- the FLT import `Definitions.Def_JacJ1Iface` (an FLT interface module for Jacobians) is
  dropped. The file uses nothing from it;
- 9 `p2m_open "…"` commands (an FLT command from `P2M.Util` that opens the named
  namespaces and activates their scoped extensions) are replaced by standard
  `open _root_.N₁ _root_.N₂ …` commands with the same namespaces. In the first one, the
  file-local namespace `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit_overBase.GroupLawOverBase` is dropped: it does not exist
  at that point of the file, and standard `open` rejects unknown namespaces. The file
  compiles without it;
- 17 `p2m_export "N" "a b …"` commands (an FLT command from `P2M.Util` that adds aliases
  `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by
  `export _root_.N (a b …)` with the same names (16 commands; for the 17th see the next item);
- 34 `p2m_reactivate "N₁ N₂ …"` commands (an FLT command from `P2M.Util` that re-activates
  the scoped extensions of the named namespaces) are replaced by
  `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces;
- FLT lines 56–58 declare `action_over` as
  `private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid.action_over … := (L.mul _ _ _).2`
  followed by `p2m_export "GoodReductionJacobian.RelativeGroupLaw.ActionGroupoid" "action_over"`.
  This private root-namespace form with an alias did not compile with the standard commands.
  It is replaced by `theorem action_over : L.action ι ≫ f = RelativeGroupLaw.actionSource f ι := (L.mul _ _ _).2`,
  declared in the current namespace
  `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit_overBase.GroupLawOverBase.RelativeGroupLaw.ActionGroupoid`, and the export is
  dropped. The statement and proof term are unchanged. The FLT companion action-groupoid file
  already uses exactly this form, and the later uses of `action_over` in the file resolve to
  it;
- FLT line 319 (in `orbit_subset`) uses `IsFinite.finite_preimage_singleton _ x`, which does
  not exist in the project Mathlib. It is replaced by
  `(pullback.snd (ι ≫ f) f).finite_preimage_singleton x`, the Mathlib lemma
  `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`: a locally quasi-finite,
  quasi-compact morphism has finite fibres. Here it applies to the finite morphism
  `pullback.snd`. The binder `∀ S : Finset J` of `orbit_subset` is FLT's; inside it, it
  shadows the base name `S`, which that body does not mention;
- nothing else changes. It compiles with the project Mathlib without errors.

## Content

Hypotheses of the statement module. The proof first repeats the action-groupoid lemmas of the
companion module (sections `Points`, `Shear`, `Relation`, plus `orbit_subset`, which is not
used for the theorem). Then, in namespace
`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit_overBase.GroupLawOverBase.RelativeGroupLaw.LawDescends`:

- *Base.* `base : P ⟶ S` is the map induced by `f` on the coequalizer, since
  `s ≫ f = t ≫ f`, and `p_base : p ≫ base = f`. Write `g := base`.
- *Products.* `oneP : J ×_S J ⟶ J ×_S P` (`p` on the second factor) and
  `twoP : J ×_S P ⟶ P ×_S P` (`p` on the first factor) are base changes of `p`
  (`isPullback_oneP`, `isPullback_twoP`). By the ported base-change theorem
  `AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback`, each is
  again a finite locally free quotient map, the coequalizer of the induced relation
  (`quotient_oneP`, `quotient_twoP`). This is where the hypotheses on `p`, `hR` and `hcoeq`
  are used.
- *Multiplication.* `mJ : J ×_S J ⟶ J` is the multiplication. Using commutativity
  (`mul_act_comm`), `mJ ≫ p` coequalizes the relation of `oneP` (`cond_one`), so it descends
  to `mOne : J ×_S P ⟶ P`. That map coequalizes the relation of `twoP` (`cond_two`), so it
  descends to `mP : P ×_S P ⟶ P` with `pp_mP : (oneP ≫ twoP) ≫ mP = mJ ≫ p`.
- *Inverse and unit.* The inverse `iJ` descends to `iP : P ⟶ P` (`cond_inv`, which uses
  `hE_inv` and commutativity). The unit is `eP := eJ ≫ p`. The maps `p` (flat and
  surjective), `oneP ≫ twoP` and the triple-product map `q3` are epimorphisms (`epi_p`,
  `epi_pp`, `epi_q3`).
- *Identities.* `one_mul_id`, `mul_one_id`, `inv_mul_id`, `mP_swap` and `α3_eq_β3`
  (associativity) are proved by cancelling these epimorphisms and using the identities of
  `L`.
- *Law.* `lawP : RelativeGroupLaw S g` has multiplication `(u, v) ↦ (u, v) ≫ mP`, unit
  `t ≫ eP` and inverse `u ≫ iP`. `hom` shows that `p` is multiplicative, and `comm` that `lawP`
  is commutative. `ker` shows that `x ≫ p = 1` iff `x` factors through `ι`. For "only if",
  the pullback `hR` gives a point `φ` of `E ×_S J` with `s ≫ φ = 1` and `t ≫ φ = x`, so
  `x = ι(e)·1`. For "if", `p_act` gives `(ι(e)·z) ≫ p = z ≫ p`.
- `solution` packages `g`, `p_base`, `lawP`, `hom`, `comm` and `ker`.

## Declarations

The theorem `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit_overBase.solution`, with the auxiliary declarations listed under
Content in the namespaces
`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit_overBase.GroupLawOverBase.RelativeGroupLaw.ActionGroupoid` and
`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit_overBase.GroupLawOverBase.RelativeGroupLaw.LawDescends`.

## Dependencies

Imports `Mathlib`, `Langlands.AnthropicFLT.OverBase.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction` and
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`.
That last module is in the Library (from the global quotient proof).
