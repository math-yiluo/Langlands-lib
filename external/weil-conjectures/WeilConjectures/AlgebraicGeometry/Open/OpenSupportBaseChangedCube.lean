/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenSupportCompactificationModel
import WeilConjectures.AlgebraicGeometry.Open.OpenSupportGraphExchange
import WeilConjectures.AlgebraicGeometry.Open.OpenSupportTailCube

/-! # The open-support cube in base-changed compactifications
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] openSupportCompactificationIso openRestrictionGraphIso
  sfGraphCompactificationComparison rightDerivedLowerShriekOfCompactificationBaseChangeMap'
  openSupportTailIso
  compactificationSupportBaseChangeIso derivedOpenImmersionLowerShriekBaseChangeIso

private theorem supportFactor_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {j : U ⟶ Y} [IsOpenImmersion j]
    {a : V ⟶ X} [IsOpenImmersion a] {p : V ⟶ U}
    (sq : IsPullback a p f j) (cf : Compactification f) (cp : Compactification p) :
    (openSupportCompactificationIso Λ sq cf cp).hom =
      Functor.whiskerRight (openRestrictionGraphIso Λ cp (cf.ofIsPullback sq)).hom
          D((j)_!open[ModuleCat.{u + 1} Λ]) ≫
        (openSupportTailIso Λ sq cf).hom := by
  simp only [openSupportCompactificationIso, openSupportTailIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom]

/-- The open-support cube when the output compactifications are the actual base changes. -/
theorem openSupportBaseChanged_cube
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sqU : IsPullback a p f j)
    {c : U' ⟶ U} {j' : U' ⟶ Y'} [IsOpenImmersion j']
    (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (sq' : IsPullback b p' p c)
    {a' : V' ⟶ X'} [IsOpenImmersion a'] (sqV : IsPullback a' p' f' j')
    (sqA : IsPullback b a' a g') (cf : Compactification f) (cp : Compactification p) :
    (TwoSquare.vComp
      (TwoSquare.mk _ _ _ _ (compactificationSupportBaseChangeIso Λ sq' cp).inv)
      (TwoSquare.mk _ _ _ _
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqj).hom)
      ).whiskerLeft (openSupportCompactificationIso Λ sqU cf cp).hom =
    (TwoSquare.vComp
      (TwoSquare.mk _ _ _ _
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqA).hom)
      (TwoSquare.mk _ _ _ _ (compactificationSupportBaseChangeIso Λ sq cf).inv)
      ).whiskerRight
        (openSupportCompactificationIso Λ sqV
          (cf.ofIsPullback sq) (cp.ofIsPullback sq')).hom := by
  let A := ModuleCat.{u + 1} Λ
  let df := cf.ofIsPullback sq
  let cq := cf.ofIsPullback sqU
  let dq := df.ofIsPullback sqV
  let z := pullback.fst cf.g g
  let k := pullback.fst cf.g j
  let k' := pullback.fst df.g j'
  have hw0 : (k' ≫ z) ≫ cf.g = (dq.g ≫ c) ≫ j := by
    dsimp only [k', z, dq, df, Compactification.ofIsPullback]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      pullback.condition, Category.assoc, ← sqj.w, ← Category.assoc]
  let w : dq.Z ⟶ cq.Z := pullback.lift (k' ≫ z) (dq.g ≫ c) hw0
  have hw : w ≫ k = k' ≫ z := pullback.lift_fst _ _ _
  have hwp : w ≫ cq.g = dq.g ≫ c := pullback.lift_snd _ _ _
  have hp : IsPullback w dq.g cq.g c := by
    have h := (IsPullback.of_hasPullback df.g j').paste_horiz
      (IsPullback.of_hasPullback cf.g g)
    change IsPullback (k' ≫ z) dq.g cf.g (j' ≫ g) at h
    rw [← sqj.w] at h
    exact (hw.symm ▸ h).of_right hwp (IsPullback.of_hasPullback cf.g j)
  have hiw : b ≫ cq.i = dq.i ≫ w := by
    apply pullback.hom_ext
    · dsimp only [cq, dq, k, k', z, w, df]
      simp only [Category.assoc, pullback.lift_fst,
        Compactification.ofIsPullback_i_fst_assoc, Compactification.ofIsPullback_i_fst]
      exact (reassoc_of% sqA.w) cf.i
    · change (b ≫ cq.i) ≫ cq.g = (dq.i ≫ w) ≫ cq.g
      simp only [Category.assoc, hwp]
      rw [← cq.comm, ← Category.assoc dq.i dq.g c, ← dq.comm]
      exact sq'.w
  have hi : IsPullback b dq.i cq.i w := by
    apply IsPullback.of_bot (t := hp) (p := hiw)
    rw [← cq.comm, ← dq.comm]
    exact sq'
  let e := openRestrictionGraphIso Λ cp cq
  let e' := openRestrictionGraphIso Λ (cp.ofIsPullback sq') dq
  let ep := compactificationSupportBaseChangeIso Λ sq' cp
  let ef := compactificationSupportBaseChangeIso Λ sq cf
  ext K
  have hG := congr_app (openRestrictionGraphIso_cartesianExchange Λ sq'
    cp cq dq w hi hp) K
  have hT := openSupportTail_cube Λ sq sqU sqj sq' sqV sqA cf w hi hp hw K
  have hn := (derivedOpenImmersionLowerShriekBaseChangeIso A sqj).hom.naturality
    (e.hom.app K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hG
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [supportFactor_hom, supportFactor_hom]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  change D((j')_!open[A]).map (ep.inv.app K) ≫
      (derivedOpenImmersionLowerShriekBaseChangeIso A sqj).hom.app _ ≫
      L((g)^*[A]).map (D((j)_!open[A]).map (e.hom.app K)) ≫
      L((g)^*[A]).map ((openSupportTailIso Λ sqU cf).hom.app K) =
    D((j')_!open[A]).map (e'.hom.app _) ≫
      (openSupportTailIso Λ sqV df).hom.app _ ≫
      Rf_!(df)[A].map
        ((derivedOpenImmersionLowerShriekBaseChangeIso A sqA).hom.app K) ≫
      ef.inv.app _
  apply (cancel_epi (D((j')_!open[A]).map (ep.hom.app K))).1
  apply (cancel_mono (ef.hom.app (D((a)_!open[A]).obj K))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
  dsimp only [rightDerivedLowerShriekOfCompactification, Functor.comp_obj,
    Functor.comp_map] at hn hT hG ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hT]
  have hG' := congrArg (D((j')_!open[A]).map) hG
  simp only [Functor.map_comp] at hG'
  dsimp only [e, e', ep] at hG' ⊢
  have he : (compactificationSupportBaseChangeIso Λ sq' cp).hom =
      rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq' cp := by
    unfold compactificationSupportBaseChangeIso
    rfl
  rw [he, ← reassoc_of% hG']
  dsimp only [A, df, cq, dq]
  erw [Category.comp_id]

end AlgebraicGeometry.Etale
