/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HorizontalDualityMateComparisons
public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.RectangleQCohComparisonLifts
import WeilConjectures.AlgebraicGeometry.RectangleQCohOrdinaryCompatibility
import WeilConjectures.AlgebraicGeometry.HorizontalTransferInverseFormula

/-! # Forward ordinary geometric pasting with fixed comparisons

Source: Stacks Project, Tags 0ATM and 0ATR.
(blueprint: lem-sc-horizontal-ordinary-forward-fixed-pasting).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- The canonical ordinary transfer square for a scheme isomorphism over a base.
Source: Stacks Project, Tags 0D5S, 0D5T and 0ATR.
(blueprint: def-sc-horizontal-ordinary-transfer).

Its data are constructed from the pinned direct-image composition, right-adjoint
uniqueness for pullback, and the inverse unit of the explicit equivalence. -/
noncomputable def horizontalOrdinaryTransfer
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P Q Z : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (e : P ≅ Q) (q : Q ⟶ Z) (p : P ⟶ Z)
    [QuasiCompact q] [QuasiSeparated q] [QuasiCompact p] [QuasiSeparated p]
    (hp : e.hom ≫ q = p) :
    TwoSquare (horizontalMatePullback e.hom) (horizontalMatePushforward q)
      (horizontalMatePushforward p) (𝟭 (schemeDerivedQCohCategory Z)) :=
  let ev := horizontalMateEquivalence e
  let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
  let li := eqToIso (congrArg qcDirectImage hp.symm) ≪≫
    horizontalMatePushComp e.hom q ≪≫
    Functor.isoWhiskerRight ri (horizontalMatePushforward q)
  .mk _ _ _ _ <|
    (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
      (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
      (Functor.rightUnitor (horizontalMatePushforward q)).inv

/-- The fixed upper comparison, with the same three factors as the pinned family.
Source: Stacks Project, Tags 0D5S and 0ATR.
(blueprint: def-sc-horizontal-ordinary-upper-comparison). -/
noncomputable def horizontalOrdinaryUpperComparison
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}} (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S) :
    qcPullback (pullback.fst f g) ⋙ qcPullback (pullback.fst (pullback.snd f g) h) ≅
      qcPullback (pullback.fst f (h ≫ g)) ⋙
        qcPullback (pullbackLeftPullbackSndIso f g h).hom :=
  horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
    eqToIso (congrArg horizontalMatePullback
      (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
    (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
      (pullback.fst f (h ≫ g))).symm

/-- The fixed base comparison, with the QCoh functors displayed in its signature.
Source: Stacks Project, Tag 0D5S.
(blueprint: def-sc-horizontal-ordinary-base-comparison). -/
noncomputable def horizontalOrdinaryBaseComparison
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {Y S T : Scheme.{u}} (g : S ⟶ Y) (h : T ⟶ S) :
    qcPullback g ⋙ qcPullback h ≅ qcPullback (h ≫ g) := horizontalMateComp h g

private theorem horizontalMateComp_hom_app
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (E : schemeDerivedQCohCategory C) :
    (schemeDerivedQCohProperty A).ι.map ((horizontalMateComp f g).hom.app E) =
      (horizontalMateAmbientComp f g).hom.app E.obj := by
  rw [horizontalMateComp, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  rfl

private theorem horizontalMateComp_inv_app
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (E : schemeDerivedQCohCategory C) :
    (schemeDerivedQCohProperty A).ι.map ((horizontalMateComp f g).inv.app E) =
      (horizontalMateAmbientComp f g).inv.app E.obj := by
  rw [horizontalMateComp, Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  rfl

private theorem cancel_ordinary_comparisons
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {A B : C} {M M' N : D} (s : A ≅ B) (j : Q.obj B ≅ N) (b : M ≅ M')
    (outer : M ⟶ N) (inner : M' ⟶ Q.obj A)
    (past : outer ≫ j.inv ≫ Q.map s.inv = b.hom ≫ inner) :
    b.inv ≫ outer = inner ≫ Q.map s.hom ≫ j.hom := by
  have h := congrArg (fun v ↦ b.inv ≫ v ≫ Q.map s.hom ≫ j.hom) past
  simpa only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id_assoc] using h

-- Type checking the pinned adjunction/comparison families needs additional kernel reductions.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A single component of the fixed-comparison mate calculation.
Source: Stacks Project, Tags 0ATM and 0D5S.
Proof: transpose the component under the pinned adjunction, apply the two
derived base-change pasting laws, and cancel units and counits.
(blueprint: lem-sc-horizontal-ordinary-forward-fixed-pasting-core-aux) -/
theorem horizontal_ordinary_forward_fixed_pasting_core_aux
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y') (E : schemeDerivedQCohCategory X) :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalOrdinaryUpperComparison f g h
    let e := pullbackLeftPullbackSndIso f g h
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let k := horizontalOrdinaryTransfer e q p (pullbackLeftPullbackSndIso_hom_snd f g h)
    let β := qcBaseChange f (h ≫ g)
    let γ := fun E : schemeDerivedQCohCategory X ↦
      (qcPullback h).map ((qcBaseChange f g).app E) ≫
        (@qcBaseChange _ (pullback f g) Y' Z _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _ h).app ((qcPullback (pullback.fst f g)).obj E)
    (horizontalOrdinaryBaseComparison g h).hom.app ((qcDirectImage f).obj E) ≫
          β.app E =
        γ E ≫ (qcDirectImage p).map (s.hom.app E) ≫
          k.app ((qcPullback (pullback.fst f (h ≫ g))).obj E) := by
  classical
  let := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
  let := quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
  intro s e q p k β γ
  obtain ⟨j, b, hj, hb⟩ := rectangle_qcoh_comparison_lifts f g h e.hom
    (pullbackLeftPullbackSndIso_hom_fst f g h)
    (pullbackLeftPullbackSndIso_hom_snd f g h)
  have hs : ∀ E : schemeDerivedQCohCategory X,
      (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
          (s.inv.app E) =
        (horizontalMateAmbientComp e.hom (pullback.fst f (h ≫ g))).hom.app E.obj ≫
          eqToHom (congrArg (fun r ↦ (derivedPullback r).obj E.obj)
            (pullbackLeftPullbackSndIso_hom_fst f g h)) ≫
          (horizontalMateAmbientComp (pullback.fst (pullback.snd f g) h)
            (pullback.fst f g)).inv.app E.obj := by
    intro E
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        simp only [s, e, horizontalOrdinaryUpperComparison, Iso.trans_inv,
          NatTrans.comp_app, Iso.symm_inv, eqToIso.inv, Functor.map_comp,
          horizontalMateComp_hom_app, horizontalMateComp_inv_app, eqToHom_map,
          eqToHom_app, Category.assoc]
  have hL : (qcPullback e.hom).IsEquivalence :=
    (horizontalMateEquivalence e).isEquivalence_functor
  have rect := rectangle_qcoh_ordinary_compatibility f g h e.hom
    (pullbackLeftPullbackSndIso_hom_fst f g h)
    (pullbackLeftPullbackSndIso_hom_snd f g h) s.symm hL hs j b hj hb E
  have hk := horizontal_transfer_eq_of_inverse_formula e q p
    (pullbackLeftPullbackSndIso_hom_snd f g h) k rfl j hj
  have hb' : b = (horizontalOrdinaryBaseComparison g h).symm := by
    apply Iso.ext
    ext D
    change (schemeDerivedQCohProperty Z).ι.map (b.hom.app D) =
      (schemeDerivedQCohProperty Z).ι.map
        ((horizontalOrdinaryBaseComparison g h).inv.app D)
    rw [hb D]
    change (horizontalMateAmbientComp h g).inv.app D.obj =
      (schemeDerivedQCohProperty Z).ι.map ((horizontalMateComp h g).inv.app D)
    exact (horizontalMateComp_inv_app h g D).symm
  change β.app E ≫ j.inv.app ((qcPullback (pullback.fst f (h ≫ g))).obj E) ≫
      (qcDirectImage p).map (s.inv.app E) = b.hom.app ((qcDirectImage f).obj E) ≫ γ E
    at rect
  have hrect := cancel_ordinary_comparisons (qcDirectImage p) (s.app E)
    (j.app ((qcPullback (pullback.fst f (h ≫ g))).obj E))
    (b.app ((qcDirectImage f).obj E)) (β.app E) (γ E) rect
  have hkE : k.app ((qcPullback (pullback.fst f (h ≫ g))).obj E) =
      j.hom.app ((qcPullback (pullback.fst f (h ≫ g))).obj E) :=
    hk ((qcPullback (pullback.fst f (h ≫ g))).obj E)
  have hbE : b.inv.app ((qcDirectImage f).obj E) =
      (horizontalOrdinaryBaseComparison g h).hom.app ((qcDirectImage f).obj E) :=
    congrArg (fun z ↦ z.inv.app ((qcDirectImage f).obj E)) hb'
  exact (congrArg (fun z ↦ z ≫ β.app E) hbE.symm).trans
    (hrect.trans (congrArg (fun z ↦ γ E ≫ (qcDirectImage p).map (s.hom.app E) ≫ z)
      hkE.symm))


/- Fixed-comparison mate calculation for ordinary forward pasting.
Source: Stacks Project, Tags 0ATM and 0D5S.
Proof: transpose under the pinned adjunction and apply the two derived
base-change pasting laws, then cancel units and counits.
(blueprint: lem-sc-horizontal-ordinary-forward-fixed-pasting-core) -/
theorem horizontal_ordinary_forward_fixed_pasting_core
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y') :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalOrdinaryUpperComparison f g h
    let e := pullbackLeftPullbackSndIso f g h
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let k := horizontalOrdinaryTransfer e q p (pullbackLeftPullbackSndIso_hom_snd f g h)
    let β := qcBaseChange f (h ≫ g)
    let γ := fun E : schemeDerivedQCohCategory X ↦
      (qcPullback h).map ((qcBaseChange f g).app E) ≫
        (@qcBaseChange _ (pullback f g) Y' Z _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _ h).app ((qcPullback (pullback.fst f g)).obj E)
    ∀ E : schemeDerivedQCohCategory X,
      (horizontalOrdinaryBaseComparison g h).hom.app ((qcDirectImage f).obj E) ≫
          β.app E =
        γ E ≫ (qcDirectImage p).map (s.hom.app E) ≫
          k.app ((qcPullback (pullback.fst f (h ≫ g))).obj E) := by
  dsimp
  intro E
  exact horizontal_ordinary_forward_fixed_pasting_core_aux g f h E


/-- Forward ordinary base-change pasting with supplied comparisons equal to the canonical ones.
Source: Stacks Project, Tags 0ATM, 08HY and 0D5S.
Proof: substitute the supplied equalities and apply the fixed-comparison core theorem.
(blueprint: lem-sc-horizontal-ordinary-forward-fixed-pasting) -/
theorem horizontal_ordinary_forward_fixed_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y') :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalOrdinaryUpperComparison f g h
    let e := pullbackLeftPullbackSndIso f g h
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let k := horizontalOrdinaryTransfer e q p (pullbackLeftPullbackSndIso_hom_snd f g h)
    let β := qcBaseChange f (h ≫ g)
    let γ := fun E : schemeDerivedQCohCategory X ↦
      (qcPullback h).map ((qcBaseChange f g).app E) ≫
        (@qcBaseChange _ (pullback f g) Y' Z _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _ h).app ((qcPullback (pullback.fst f g)).obj E)
    ∀ (s' : qcPullback (pullback.fst f g) ⋙
        qcPullback (pullback.fst (pullback.snd f g) h) ≅
        qcPullback (pullback.fst f (h ≫ g)) ⋙ qcPullback e.hom)
      (k' : TwoSquare (horizontalMatePullback e.hom)
        (horizontalMatePushforward q) (horizontalMatePushforward p)
        (𝟭 (schemeDerivedQCohCategory Z))),
      s' = s → k' = k → ∀ E : schemeDerivedQCohCategory X,
      (horizontalOrdinaryBaseComparison g h).hom.app ((qcDirectImage f).obj E) ≫
          β.app E =
        γ E ≫ (qcDirectImage p).map (s'.hom.app E) ≫
          k'.app ((qcPullback (pullback.fst f (h ≫ g))).obj E) := by
  classical
  dsimp
  intro s' k' hs hk
  subst s'
  subst k'
  exact horizontal_ordinary_forward_fixed_pasting_core g f h

end AlgebraicGeometry
