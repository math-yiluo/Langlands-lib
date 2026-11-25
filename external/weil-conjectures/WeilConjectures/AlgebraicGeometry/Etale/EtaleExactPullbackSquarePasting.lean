/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Exact derived pullback-square pasting

Source: Stacks Project, Tag 03S6; coherence of exact inverse images.
(blueprint: lem-pur-etale-exact-pullback-square-pasting).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactDerivedPasting
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar Functor.mapDerivedCategory
  unboundedEtaleUpperStarCompIso exactDerivedSquareUpperStarIso

private lemma exact_word_cell_iso
    {I : Type*} (C : I → Type*) [∀ i, Category (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory (C i)] {i j : I}
    {P R : Word C i j}
    (alpha : P.ordinary.obj ≅ R.ordinary.obj) :
    Word.cell C alpha.hom = P.comparison.inv ≫
      (Functor.mapDerivedCategoryNatIso alpha).hom ≫ R.comparison.hom := rfl

/-- Inverse exact pullback-square comparisons paste under successive Cartesian changes.
Source: Stacks Project, Tag 03S6, and the sheaf inverse-image square-pasting law.
(blueprint: lem-pur-etale-exact-pullback-square-pasting).

Proof: Apply the ordinary square-pasting law to the flipped squares. The comparison for
such a square is the inverse of the original comparison. Cancel the source compositor
and apply the target compositor to obtain the displayed inverse-square equation on sheaves.
Encode its two sides as finite expressions in exact inverse-image functors and square and
compositor cells. Exact-derived transformation pasting descends this equation. Its word
comparison formula identifies the derived square cells with exactDerivedSquareUpperStarIso
and the two compositor cells with unboundedEtaleUpperStarCompIso. Evaluation at K proves
the equation on the entire unbounded category. No finiteness or Noetherian assumption is
used; identity arrows and empty schemes are included. -/
theorem etaleExactPullbackSquarePasting
    (A : Type (u + 1)) [CommRing A]
    {U U' U'' X X' X'' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {e'' : U'' ⟶ X''}
    {w : X' ⟶ X} {z : X'' ⟶ X'} {w' : U' ⟶ U} {z' : U'' ⟶ U'}
    (sq : IsPullback w' e' e w) (sq' : IsPullback z' e'' e' z)
    (sq'' : IsPullback (z' ≫ w') e'' e (z ≫ w))
    (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) z').mapDerivedCategory.map ((exactDerivedSquareUpperStarIso
        (ModuleCat.{u + 1} A) sq.toCommSq).inv.app K) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq'.toCommSq).inv.app ((upperStar
          (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) =
    (unboundedEtaleUpperStarCompIso A z' w').inv.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq''.toCommSq).inv.app K ≫
      (upperStar (ModuleCat.{u + 1} A) e'').mapDerivedCategory.map
        ((unboundedEtaleUpperStarCompIso A z w).hom.app K) := by
  let M := ModuleCat.{u + 1} A
  have ho (N : Sheaf X.smallEtaleTopology M) :
      (upperStar.{u + 2, u} M z').map
          ((squareUpperStarIso.{u + 2, u} M sq.toCommSq).inv.app N) ≫
        (squareUpperStarIso.{u + 2, u} M sq'.toCommSq).inv.app
          ((upperStar.{u + 2, u} M w).obj N) =
        (upperStarComp.{u + 2, u} M z' w' (z' ≫ w') rfl).inv.app
          ((upperStar.{u + 2, u} M e).obj N) ≫
        (squareUpperStarIso.{u + 2, u} M sq''.toCommSq).inv.app N ≫
        (upperStar.{u + 2, u} M e'').map
          ((upperStarComp.{u + 2, u} M z w (z ≫ w) rfl).hom.app N) := by
    have h := congr_app (squareUpperStarIso_paste_vert_hom.{u + 2, u} M
      sq'.toCommSq.flip sq.toCommSq.flip sq''.toCommSq.flip) N
    change (squareUpperStarIso.{u + 2, u} M sq''.toCommSq.flip).hom.app N =
      (upperStarComp.{u + 2, u} M z' w' (z' ≫ w') rfl).hom.app
        ((upperStar.{u + 2, u} M e).obj N) ≫
      (upperStar.{u + 2, u} M z').map
        ((squareUpperStarIso.{u + 2, u} M sq.toCommSq.flip).hom.app N) ≫
      (squareUpperStarIso.{u + 2, u} M sq'.toCommSq.flip).hom.app
        ((upperStar.{u + 2, u} M w).obj N) ≫
      (upperStar.{u + 2, u} M e'').map
        ((upperStarComp.{u + 2, u} M z w (z ≫ w) rfl).inv.app N) at h
    rw [squareUpperStarIso_flip M sq''.toCommSq,
      squareUpperStarIso_flip M sq.toCommSq,
      squareUpperStarIso_flip M sq'.toCommSq] at h
    have h' := congrArg
      (fun f ↦ (upperStarComp.{u + 2, u} M z' w' (z' ≫ w') rfl).inv.app
        ((upperStar.{u + 2, u} M e).obj N) ≫ f ≫
        (upperStar.{u + 2, u} M e'').map
          ((upperStarComp.{u + 2, u} M z w (z ≫ w) rfl).hom.app N)) h
    simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc] at h'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
    exact h'.symm
  let C : Fin 6 → Type (u + 2) := fun i ↦
    Sheaf ((![X, X', X'', U, U', U'']) i).smallEtaleTopology M
  let E : Word C 0 3 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M e))
  let E' : Word C 1 4 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M e'))
  let E'' : Word C 2 5 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M e''))
  let W : Word C 0 1 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M w))
  let Z : Word C 1 2 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M z))
  let V : Word C 0 2 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M (z ≫ w)))
  let W' : Word C 3 4 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M w'))
  let Z' : Word C 4 5 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M z'))
  let V' : Word C 3 5 :=
    .edge (ExactFunctor.of (upperStar.{u + 2, u} M (z' ≫ w')))
  let q : Expression C (.comp E W') (.comp W E') :=
    .cell (squareUpperStarIso.{u + 2, u} M sq.toCommSq).inv
  let q' : Expression C (.comp E' Z') (.comp Z E'') :=
    .cell (squareUpperStarIso.{u + 2, u} M sq'.toCommSq).inv
  let q'' : Expression C (.comp E V') (.comp V E'') :=
    .cell (squareUpperStarIso.{u + 2, u} M sq''.toCommSq).inv
  let a : Expression C (.comp W' Z') V' :=
    .cell (upperStarComp.{u + 2, u} M z' w' (z' ≫ w') rfl).inv
  let b : Expression C V (.comp W Z) :=
    .cell (upperStarComp.{u + 2, u} M z w (z ≫ w) rfl).hom
  let lhs : Expression C
      (.comp (.comp E W') Z') (.comp W (.comp Z E'')) :=
    .vcomp (.output q Z') (.vcomp (.assoc W E' Z') (.input W q'))
  let rhs : Expression C
      (.comp (.comp E W') Z') (.comp W (.comp Z E'')) :=
    .vcomp (.assoc E W' Z') (.vcomp (.input E a)
      (.vcomp q'' (.vcomp (.output b E'') (.assoc W Z E''))))
  have hordinary : lhs.ordinary = rhs.ordinary := by
    apply NatTrans.ext
    funext N
    simpa [lhs, rhs, q, q', q'', a, b,
      Expression.ordinary,
      E, E', E'', W, Z, V, W', Z', V',
      Word.ordinary] using ho N
  have hd := (exact_derived_transformation_pasting C).2.1
    lhs rhs hordinary
  have hq : q.derived = (exactDerivedSquareUpperStarIso M sq.toCommSq).inv := by
    change Word.cell C
      (P := .comp E W') (R := .comp W E')
      (squareUpperStarIso.{u + 2, u} M sq.toCommSq).symm.hom = _
    rw [exact_word_cell_iso]
    simp [E, E', W, W', Word.comparison,
      Word.ordinary, exactDerivedSquareUpperStarIso,
      Functor.mapDerivedCategoryNatIso_symm]
  have hq' : q'.derived = (exactDerivedSquareUpperStarIso M sq'.toCommSq).inv := by
    change Word.cell C
      (P := .comp E' Z') (R := .comp Z E'')
      (squareUpperStarIso.{u + 2, u} M sq'.toCommSq).symm.hom = _
    rw [exact_word_cell_iso]
    simp [E', E'', Z, Z', Word.comparison,
      Word.ordinary, exactDerivedSquareUpperStarIso,
      Functor.mapDerivedCategoryNatIso_symm]
  have hq'' : q''.derived = (exactDerivedSquareUpperStarIso M sq''.toCommSq).inv := by
    change Word.cell C
      (P := .comp E V') (R := .comp V E'')
      (squareUpperStarIso.{u + 2, u} M sq''.toCommSq).symm.hom = _
    rw [exact_word_cell_iso]
    simp [E, E'', V, V', Word.comparison,
      Word.ordinary, exactDerivedSquareUpperStarIso,
      Functor.mapDerivedCategoryNatIso_symm]
  have ha : a.derived = (unboundedEtaleUpperStarCompIso A z' w').inv := by
    change Word.cell C
      (P := .comp W' Z') (R := V') (upperStarComp.{u + 2, u} M z' w' (z' ≫ w') rfl).symm.hom = _
    rw [exact_word_cell_iso]
    simp [W', Z', V', Word.comparison,
      Word.ordinary, unboundedEtaleUpperStarCompIso, M,
      Functor.mapDerivedCategoryNatIso_symm]
  have hb : b.derived = (unboundedEtaleUpperStarCompIso A z w).hom := by
    change Word.cell C
      (P := V) (R := .comp W Z) (upperStarComp.{u + 2, u} M z w (z ≫ w) rfl).hom = _
    rw [exact_word_cell_iso]
    simp only [Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Nat.succ_eq_add_one, Nat.reduceAdd, Word.ordinary, ExactFunctor.of_fst,
      Word.comparison, Iso.refl_inv, Functor.isoWhiskerRight_refl,
      Functor.isoWhiskerLeft_refl, Iso.trans_refl, unboundedEtaleUpperStarCompIso,
      Iso.trans_hom, V, M, W, Z]
    erw [Category.id_comp]
  have h := congr_app hd K
  simpa only [lhs, rhs, Expression.derived,
    hq, hq', hq'', ha, hb, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    E, E', E'', W, Z, V, W', Z', V', Word.derived,
    Word.ordinary, ExactFunctor.of,
    Category.id_comp, Category.comp_id, Category.assoc] using h

end AlgebraicGeometry.Etale
