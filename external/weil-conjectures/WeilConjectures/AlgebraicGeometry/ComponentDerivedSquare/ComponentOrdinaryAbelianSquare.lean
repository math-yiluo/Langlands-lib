/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import all WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentLiftBaseChange
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

set_option linter.privateModule false

/-! # Coefficient-normalized abelian component square

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

private lemma adjunction_comp_assoc
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : C ⥤ D} {R'' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') :
    (a.comp b).comp c = a.comp (b.comp c) := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc]

private lemma conjugate_right_transport
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₁' R₂ R₂' : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₁') (d : R₂ ≅ R₂')
    (τ : L₂ ⟶ L₁) :
    conjugateEquiv (a.ofNatIsoRight e) (b.ofNatIsoRight d) τ =
      e.inv ≫ conjugateEquiv a b τ ≫ d.hom := by
  ext X
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← d.hom.naturality_assoc, ← d.hom.naturality_assoc, ← d.hom.naturality]
  rw [← R₂.map_comp_assoc, ← τ.naturality, R₂.map_comp_assoc]
  rw [← b.unit_naturality_assoc]

private lemma adjunction_right_transport_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R R' : B ⥤ A} {L' : B ⥤ C} {S : C ⥤ B}
    (a : L ⊣ R) (b : L' ⊣ S) (e : R ≅ R') :
    (a.ofNatIsoRight e).comp b =
      (a.comp b).ofNatIsoRight (Functor.isoWhiskerLeft S e) := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  simpa only [Functor.comp_obj, Functor.id_obj, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc] using congrArg (fun m ↦ a.unit.app X ≫ m)
      (e.hom.naturality (b.unit.app (L.obj X))).symm

private lemma sheaf_trans_ext
    {C D A : Type*} [Category C] [Category D] [Category A]
    (J : GrothendieckTopology C) {F G : D ⥤ Sheaf J A} {α β : F ⟶ G}
    (h : ∀ (M : D) (U : C), (α.app M).hom.app (op U) = (β.app M).hom.app (op U)) :
    α = β := by
  apply NatTrans.ext
  funext M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact h M U.unop

private lemma conjugateIso_symm_inv
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv b a (((conjugateIsoEquiv a b).symm e).inv) = e.inv := by
  exact (conjugateEquiv b a).apply_symm_apply e.inv

private lemma beta_pasting
    {C D E A B : Type*} [Category C] [Category D] [Category E] [Category A] [Category B]
    {P : C ⥤ D} {RP : D ⥤ C} {Q : C ⥤ E} {RQ : E ⥤ C}
    {SX : D ⥤ A} {RX : A ⥤ D} {SY : E ⥤ B} {RY : B ⥤ E}
    {H : D ⥤ E} {RH : E ⥤ D} {F : A ⥤ B} {R : B ⥤ A}
    {AX : C ⥤ A} {BX : A ⥤ C} {AY : C ⥤ B} {BY : B ⥤ C}
    (aP : P ⊣ RP) (aQ : Q ⊣ RQ) (sx : SX ⊣ RX) (sy : SY ⊣ RY)
    (sh : H ⊣ RH) (af : F ⊣ R) (ax : AX ⊣ BX) (ay : AY ⊣ BY)
    (bx : P ⋙ SX ≅ AX) (by' : Q ⋙ SY ≅ AY) (bh : P ⋙ H ≅ Q)
    (a : SX ⋙ F ≅ H ⋙ SY) (c : AX ⋙ F ≅ AY)
    (h : Functor.whiskerLeft R (conjugateEquiv (aP.comp sx) ax bx.inv) ≫
          conjugateEquiv (ax.comp af) ay c.inv =
        Functor.whiskerRight (conjugateEquiv (sx.comp af) (sh.comp sy) a.inv) RP ≫
          Functor.whiskerLeft RY (conjugateEquiv (aP.comp sh) aQ bh.inv) ≫
          conjugateEquiv (aQ.comp sy) ay by'.inv) :
    (Functor.isoWhiskerRight bx F ≪≫ c).hom =
      (Functor.isoWhiskerLeft P a ≪≫ Functor.isoWhiskerRight bh SY ≪≫ by').hom := by
  let p := Functor.isoWhiskerRight bx F ≪≫ c
  let q := Functor.isoWhiskerLeft P a ≪≫ Functor.isoWhiskerRight bh SY ≪≫ by'
  have hp : conjugateEquiv (aP.comp (sx.comp af)) ay p.inv =
      Functor.whiskerLeft R (conjugateEquiv (aP.comp sx) ax bx.inv) ≫
        conjugateEquiv (ax.comp af) ay c.inv := by
    dsimp only [p, Iso.trans_inv, Functor.isoWhiskerRight_inv]
    rw [← adjunction_comp_assoc, ← conjugateEquiv_comp _ (ax.comp af)]
    exact congrArg (fun m ↦ m ≫ conjugateEquiv (ax.comp af) ay c.inv)
      (conjugateEquiv_whiskerRight (aP.comp sx) ax af bx.inv)
  have hqin : q.inv =
      (by'.inv ≫ Functor.whiskerRight bh.inv SY) ≫ Functor.whiskerLeft P a.inv := by
    simp only [q, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Category.assoc]
  have hq : conjugateEquiv (aP.comp (sx.comp af)) ay q.inv =
      Functor.whiskerRight (conjugateEquiv (sx.comp af) (sh.comp sy) a.inv) RP ≫
        Functor.whiskerLeft RY (conjugateEquiv (aP.comp sh) aQ bh.inv) ≫
        conjugateEquiv (aQ.comp sy) ay by'.inv := by
    rw [hqin, ← conjugateEquiv_comp _ (aP.comp (sh.comp sy)),
      conjugateEquiv_whiskerLeft, ← adjunction_comp_assoc,
      ← conjugateEquiv_comp _ (aQ.comp sy)]
    exact congrArg
      (fun m ↦ Functor.whiskerRight (conjugateEquiv (sx.comp af) (sh.comp sy) a.inv) RP ≫
        m ≫ conjugateEquiv (aQ.comp sy) ay by'.inv)
      (conjugateEquiv_whiskerRight (aP.comp sh) aQ sy bh.inv)
  have hi : p.inv = q.inv :=
    (conjugateEquiv (aP.comp (sx.comp af)) ay).injective (hp.trans (h.trans hq.symm))
  change p.hom = q.hom
  apply (cancel_mono p.inv).1
  rw [p.hom_inv_id, hi, q.hom_inv_id]
  all_goals rfl

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare


private def testComparison {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) :
    CondensedRing.componentTests X ⋙ Scheme.proEtaleBaseChange f ≅
      Over.pullback (affineComponentMap f) ⋙ CondensedRing.componentTests Y :=
  ((Scheme.ProEt.forgetFullyFaithful Y).whiskeringRight _).preimageIso
    (component_lift_base_change.choose f)

private def directComparison
    (Λ : Profinite.CondensedRing.{u}) {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) (sX : Corner Λ X) (sY : Corner Λ Y) :
    componentDirect Y sY.continuous ⋙ sliceDirect (affineComponentMap f) ≅
      lowerStar Ab.{u + 1} f ⋙ componentDirect X sX.continuous := by
  letI := sX.continuous
  letI := sY.continuous
  letI := Functor.isContinuous_comp (Over.pullback (affineComponentMap f))
    (CondensedRing.componentTests Y) ((coherentTopology Profinite.{u}).over
      (affineComponentSpace X)) ((coherentTopology Profinite.{u}).over
      (affineComponentSpace Y)) (Scheme.ProEt.topology Y)
  letI := Functor.isContinuous_comp (CondensedRing.componentTests X)
    (Scheme.proEtaleBaseChange f) ((coherentTopology Profinite.{u}).over
      (affineComponentSpace X)) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
  exact Functor.sheafPushforwardContinuousComp'
      (testComparison f).symm Ab.{u + 1} _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (Iso.refl (CondensedRing.componentTests X ⋙ Scheme.proEtaleBaseChange f))
      Ab.{u + 1} _ _ _).symm

private lemma directComparison_inv_app
    (Λ : Profinite.CondensedRing.{u}) {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) (sX : Corner Λ X) (sY : Corner Λ Y)
    (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (E : Over (affineComponentSpace X)) :
    (((directComparison Λ f sX sY).inv.app G).hom.app (op E)) =
      G.obj.map ((testComparison f).inv.app E).op := by
  simp only [Functor.comp_obj, directComparison, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.refl_inv,
    NatTrans.id_app, op_id, CategoryTheory.Functor.map_id,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.symm_hom]
  exact Category.id_comp _

private def abelianComparison
    (Λ : Profinite.CondensedRing.{u}) {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (sX : Corner Λ X) (sY : Corner Λ Y) (sh : Slice Λ (affineComponentMap f)) :
    sX.inverse ⋙ upperStar Ab.{u + 1} f ≅ sh.inverse ⋙ sY.inverse :=
  (conjugateIsoEquiv (sh.adjunction.comp sY.adjunction)
    (sX.adjunction.comp (upperStarLowerStarAdjunction Ab.{u + 1} f))).symm
      (directComparison Λ f sX sY)

private def absoluteAdjunctionAlong {X : Scheme.{u}} (g : X ⟶ specZ) :=
  (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} g)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp profiniteToProEt
        (Scheme.proEtaleBaseChange g) Ab.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
        (Scheme.ProEt.topology X))

private def absoluteTestMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (g : X ⟶ specZ) (k : Y ⟶ specZ) (w : f ≫ g = k) (S : Profinite.{u}) :
    ((profiniteToProEt ⋙ Scheme.proEtaleBaseChange k).obj S) ⟶
      ((profiniteToProEt ⋙ Scheme.proEtaleBaseChange g ⋙
        Scheme.proEtaleBaseChange f).obj S) :=
  (MorphismProperty.Over.pullbackComp f g (fg := k) (hfg := w.symm)).hom.app
    (profiniteToProEt.obj S)

private lemma absoluteComparison_mate_along {X Y : Scheme.{u}} (f : Y ⟶ X)
    (g : X ⟶ specZ) (k : Y ⟶ specZ) (w : f ≫ g = k)
    (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (S : Profinite.{u}) :
    (((conjugateEquiv
      ((absoluteAdjunctionAlong g).comp (upperStarLowerStarAdjunction Ab.{u + 1} f))
      (absoluteAdjunctionAlong k)
      (Functor.associator pointUpperStar (upperStar Ab.{u + 1} g)
          (upperStar Ab.{u + 1} f) ≪≫
        Functor.isoWhiskerLeft pointUpperStar
          ((upperStarComp Ab.{u + 1} f g).symm ≪≫
            eqToIso (congrArg (upperStar Ab.{u + 1}) w))).inv).app G).hom.app (op S)) =
      G.obj.map (absoluteTestMap f g k w S).op := by
  subst k
  have hα : (Functor.associator pointUpperStar (upperStar Ab.{u + 1} g)
          (upperStar Ab.{u + 1} f) ≪≫
        Functor.isoWhiskerLeft pointUpperStar
          ((upperStarComp Ab.{u + 1} f g).symm ≪≫
            eqToIso (congrArg (upperStar Ab.{u + 1}) rfl))).inv =
      Functor.whiskerLeft pointUpperStar (upperStarComp Ab.{u + 1} f g).hom := by
    ext M
    simp
  rw [hα]
  dsimp only [absoluteAdjunctionAlong]
  rw [adjunction_right_transport_comp, conjugate_right_transport,
    adjunction_comp_assoc]
  erw [conjugateEquiv_whiskerLeft, conjugateEquiv_upperStarComp_hom]
  simp only [Functor.comp_obj, pointLowerStar, Functor.isoWhiskerLeft_inv,
    lowerStarComp, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp_inv_app_hom_app,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv,
    Functor.sheafPushforwardContinuousComp_hom_app_hom_app, absoluteTestMap]
  exact (Category.id_comp _).trans (Category.comp_id _)

private lemma absoluteAdjunctionAlong_eq (X : Scheme.{u}) :
    absoluteAdjunctionAlong (toSpecZ X) = absoluteAdjunction X := by
  rfl

private lemma upperStarFromPointComp_eq {X Y : Scheme.{u}} (f : Y ⟶ X) :
    upperStarFromPointComp f =
      Functor.associator pointUpperStar (upperStar Ab.{u + 1} (toSpecZ X))
          (upperStar Ab.{u + 1} f) ≪≫
        Functor.isoWhiskerLeft pointUpperStar
          ((upperStarComp Ab.{u + 1} f (toSpecZ X)).symm ≪≫
            eqToIso (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ f))) := by
  rfl

private lemma absoluteComparison_mate {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (S : Profinite.{u}) :
    (((conjugateEquiv
      ((absoluteAdjunction X).comp (upperStarLowerStarAdjunction Ab.{u + 1} f))
      (absoluteAdjunction Y) (upperStarFromPointComp f).inv).app G).hom.app (op S)) =
      G.obj.map (absoluteTestMap f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) S).op := by
  rw [← absoluteAdjunctionAlong_eq X, ← absoluteAdjunctionAlong_eq Y,
    upperStarFromPointComp_eq]
  exact absoluteComparison_mate_along f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) G S

private lemma absoluteTestMap_projection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : Profinite.{u}) (z : ((profiniteToProEtOf Y).obj S).left) :
    profiniteTestProjection X S
      (pullback.fst ((profiniteToProEtOf X).obj S).hom f
        ((absoluteTestMap f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) S).left z)) =
      profiniteTestProjection Y S z := by
  have h : (absoluteTestMap f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) S).left ≫
      pullback.fst ((profiniteToProEtOf X).obj S).hom f ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) =
      pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ Y) := by
    dsimp only [absoluteTestMap, MorphismProperty.Over.pullbackComp]
    erw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
    simp
    rfl
  exact congrArg
    (fun m : ((profiniteToProEtOf Y).obj S).left ⟶ profiniteToScheme.obj S ↦
      (ContinuousMap.fst.comp
        ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
          (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩)
          (m z)) h

private lemma profinite_prod_ext {P Q : Profinite.{u}} {a b : (P ⨯ Q : Profinite.{u})}
    (h₁ : (prod.fst : P ⨯ Q ⟶ P) a = (prod.fst : P ⨯ Q ⟶ P) b)
    (h₂ : (prod.snd : P ⨯ Q ⟶ Q) a = (prod.snd : P ⨯ Q ⟶ Q) b) : a = b := by
  apply Concrete.isLimit_ext (pair P Q) (prodIsProd P Q) a b
  rintro ⟨j⟩
  cases j
  · exact h₁
  · exact h₂

private lemma absolute_coordinate_inv
    (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) [IsAffine X]
    (s : Corner Λ X) (S : Profinite.{u}) (z : ((profiniteToProEtOf X).obj S).left) :
    (prod.snd : affineComponentSpace X ⨯ S ⟶ S)
      (relativeComponentCoordinate X ((Over.star (affineComponentSpace X)).obj S)
        ((s.absoluteTests.inv.app S).left z)) = profiniteTestProjection X S z := by
  have hi := iso_hom_inv_apply
    ((Scheme.ProEt.forget X).mapIso (s.absoluteTests.app S)) z
  change (s.absoluteTests.hom.app S).left
    ((s.absoluteTests.inv.app S).left z) = z at hi
  simpa only [hi] using s.absolute_coordinate S ((s.absoluteTests.inv.app S).left z)

private lemma starPullback_inv_coordinate {P Q : Profinite.{u}} (h : Q ⟶ P)
    (S : Profinite.{u}) :
    ((Over.starPullbackIsoStar h).inv.app S).left ≫
      pullback.fst ((Over.star P).obj S).hom h ≫ (prod.snd : P ⨯ S ⟶ S) =
        (prod.snd : Q ⨯ S ⟶ S) := by
  simp [Over.starPullbackIsoStar]

private lemma absolute_test_square
    (Λ : Profinite.CondensedRing.{u}) {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (sX : Corner Λ X) (sY : Corner Λ Y) (S : Profinite.{u}) :
    absoluteTestMap f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) S ≫
        (Scheme.proEtaleBaseChange f).map (sX.absoluteTests.inv.app S) ≫
        (testComparison f).hom.app ((Over.star (affineComponentSpace X)).obj S) =
      sY.absoluteTests.inv.app S ≫ (CondensedRing.componentTests Y).map
        ((Over.starPullbackIsoStar (affineComponentMap f)).inv.app S) := by
  let E := (Over.star (affineComponentSpace X)).obj S
  let E' := (Over.star (affineComponentSpace Y)).obj S
  let h := affineComponentMap f
  let A := absoluteTestMap f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) S
  let B := (Scheme.proEtaleBaseChange f).map (sX.absoluteTests.inv.app S)
  let t := (testComparison f).hom.app E
  let v := sY.absoluteTests.inv.app S ≫
    (CondensedRing.componentTests Y).map ((Over.starPullbackIsoStar h).inv.app S)
  change A ≫ B ≫ t = v
  apply MorphismProperty.Over.Hom.ext
  apply lift_ext Y
  · exact (A ≫ B ≫ t).w.trans v.w.symm
  · intro z
    let a := relativeComponentCoordinate Y ((Over.pullback h).obj E)
      ((A ≫ B ≫ t).left z)
    let b := relativeComponentCoordinate Y ((Over.pullback h).obj E) (v.left z)
    have hQ : pullback.snd E.hom h a = pullback.snd E.hom h b := by
      exact (coordinate_base Y ((Over.pullback h).obj E) _).trans
        ((congrArg ConnectedComponents.mk
          (congrArg (fun m : ((profiniteToProEtOf Y).obj S).left ⟶ Y ↦ m z)
            ((A ≫ B ≫ t).w.trans v.w.symm))).trans
          (coordinate_base Y ((Over.pullback h).obj E) _).symm)
    have hE : E.hom = (prod.fst : affineComponentSpace X ⨯ S ⟶
        affineComponentSpace X) := by
      simp only [E, Over.star_obj_hom]
    apply profinite_pullback_ext E.hom h
    · apply profinite_prod_ext
      · change (prod.fst : affineComponentSpace X ⨯ S ⟶ affineComponentSpace X)
          (pullback.fst E.hom h a) =
            (prod.fst : affineComponentSpace X ⨯ S ⟶ affineComponentSpace X)
              (pullback.fst E.hom h b)
        have hp :=
          (ConcreteCategory.congr_hom
          (pullback.condition (f := E.hom) (g := h)) a).trans
            ((congrArg (fun q ↦ h q) hQ).trans
              (ConcreteCategory.congr_hom
                (pullback.condition (f := E.hom) (g := h)) b).symm)
        simp only [ConcreteCategory.comp_apply, hE] at hp
        exact hp
      · have hc := component_lift_base_change.choose_spec.1 X Y f E (B.left (A.left z))
        have hn : B.left ≫ pullback.fst ((relativeComponentLift X).obj E).hom f =
            pullback.fst ((profiniteToProEtOf X).obj S).hom f ≫
              (sX.absoluteTests.inv.app S).left := by
          simp only [Scheme.proEtaleBaseChange, MorphismProperty.Over.pullback,
            Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
            MorphismProperty.Over.homMk_hom, Over.homMk_left, B]
          exact pullback.lift_fst _ _ _
        have hc' : pullback.fst E.hom h a =
            relativeComponentCoordinate X E
              ((sX.absoluteTests.inv.app S).left
                (pullback.fst ((profiniteToProEtOf X).obj S).hom f (A.left z))) := by
          change pullback.fst E.hom h
            (relativeComponentCoordinate Y ((Over.pullback h).obj E)
              (t.left (B.left (A.left z)))) = _
          rw [show t.left = ((component_lift_base_change.choose f).hom.app E).left from rfl]
          exact hc.trans (congrArg (relativeComponentCoordinate X E)
            (congrArg (fun m : ((profiniteToProEtOf X ⋙
                Scheme.proEtaleBaseChange f).obj S).left ⟶
                ((relativeComponentLift X).obj E).left ↦ m (A.left z)) hn))
        have hv : b = ((Over.starPullbackIsoStar h).inv.app S).left
            (relativeComponentCoordinate Y E' ((sY.absoluteTests.inv.app S).left z)) :=
          coordinate_map Y ((Over.starPullbackIsoStar h).inv.app S) _
        calc
          (prod.snd : affineComponentSpace X ⨯ S ⟶ S) (pullback.fst E.hom h a) =
              profiniteTestProjection X S
                (pullback.fst ((profiniteToProEtOf X).obj S).hom f (A.left z)) := by
            rw [hc']
            exact absolute_coordinate_inv Λ X sX S _
          _ = profiniteTestProjection Y S z := absoluteTestMap_projection f S z
          _ = (prod.snd : affineComponentSpace Y ⨯ S ⟶ S)
              (relativeComponentCoordinate Y E' ((sY.absoluteTests.inv.app S).left z)) :=
            (absolute_coordinate_inv Λ Y sY S z).symm
          _ = (prod.snd : affineComponentSpace X ⨯ S ⟶ S)
              (pullback.fst E.hom h b) := by
            rw [hv]
            exact (ConcreteCategory.congr_hom (starPullback_inv_coordinate h S) _).symm
    · exact hQ

private lemma coefficient_right_mates_app
    (Λ : Profinite.CondensedRing.{u}) {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (sX : Corner Λ X) (sY : Corner Λ Y)
    (sh : Slice Λ (affineComponentMap f))
    (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (S : Profinite.{u}) :
    let P := affineComponentSpace X;
    let Q := affineComponentSpace Y;
    let aP := slicePointAdjunction P;
    let aQ := slicePointAdjunction Q;
    let af := upperStarLowerStarAdjunction Ab.{u + 1} f;
    let ax := absoluteAdjunction X;
    let ay := absoluteAdjunction Y;
    (((conjugateEquiv (aP.comp sX.adjunction) ax sX.beta.inv).app
        ((lowerStar Ab.{u + 1} f).obj G)).hom.app (op S)) ≫
      (((conjugateEquiv (ax.comp af) ay (upperStarFromPointComp f).inv).app G).hom.app (op S)) =
    (((directComparison Λ f sX sY).inv.app G).hom.app
        (op ((Over.star P).obj S))) ≫
      (((conjugateEquiv (aP.comp sh.adjunction) aQ sh.beta.inv).app
        ((componentDirect Y sY.continuous).obj G)).hom.app (op S)) ≫
      (((conjugateEquiv (aQ.comp sY.adjunction) ay sY.beta.inv).app G).hom.app (op S)) := by
  let P := affineComponentSpace X
  let Q := affineComponentSpace Y
  let aP := slicePointAdjunction P
  let aQ := slicePointAdjunction Q
  let af := upperStarLowerStarAdjunction Ab.{u + 1} f
  let ax := absoluteAdjunction X
  let ay := absoluteAdjunction Y
  have hx := sX.beta_mate ((lowerStar Ab.{u + 1} f).obj G) S
  have hy := sY.beta_mate G S
  have hh := sh.beta_mate ((componentDirect Y sY.continuous).obj G) S
  simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom] at hx hy hh
  have hγ := absoluteComparison_mate f G S
  have hδ := directComparison_inv_app Λ f sX sY G ((Over.star P).obj S)
  refine (congrArg₂ (fun a b ↦ a ≫ b) hx hγ).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b ↦ a ≫ b) hδ
    (congrArg₂ (fun a b ↦ a ≫ b) hh hy)).symm
  change G.obj.map ((Scheme.proEtaleBaseChange f).map
      (sX.absoluteTests.inv.app S)).op ≫
      G.obj.map (absoluteTestMap f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) S).op =
    G.obj.map ((testComparison f).inv.app ((Over.star P).obj S)).op ≫
      G.obj.map ((CondensedRing.componentTests Y).map
        ((Over.starPullbackIsoStar (affineComponentMap f)).inv.app S)).op ≫
      G.obj.map (sY.absoluteTests.inv.app S).op
  simp only [← G.obj.map_comp, ← op_comp]
  have hg : absoluteTestMap f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) S ≫
      (Scheme.proEtaleBaseChange f).map (sX.absoluteTests.inv.app S) =
    sY.absoluteTests.inv.app S ≫ (CondensedRing.componentTests Y).map
        ((Over.starPullbackIsoStar (affineComponentMap f)).inv.app S) ≫
      (testComparison f).inv.app ((Over.star P).obj S) := by
    apply (cancel_mono ((testComparison f).hom.app ((Over.star P).obj S))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact absolute_test_square Λ f sX sY S
  rw [hg]
  simp only [Category.assoc]

private lemma coefficient_right_mates
    (Λ : Profinite.CondensedRing.{u}) {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (sX : Corner Λ X) (sY : Corner Λ Y)
    (sh : Slice Λ (affineComponentMap f)) :
    let P := affineComponentSpace X;
    let Q := affineComponentSpace Y;
    let aP := slicePointAdjunction P;
    let aQ := slicePointAdjunction Q;
    let af := upperStarLowerStarAdjunction Ab.{u + 1} f;
    let ax := absoluteAdjunction X;
    let ay := absoluteAdjunction Y;
      Functor.whiskerLeft (lowerStar Ab.{u + 1} f)
          (conjugateEquiv (aP.comp sX.adjunction) ax sX.beta.inv) ≫
        conjugateEquiv (ax.comp af) ay (upperStarFromPointComp f).inv =
      Functor.whiskerRight (directComparison Λ f sX sY).inv
          ((Over.star P).sheafPushforwardContinuous Ab.{u + 1}
            (coherentTopology Profinite.{u}) ((coherentTopology Profinite.{u}).over P)) ≫
        Functor.whiskerLeft (componentDirect Y sY.continuous)
          (conjugateEquiv (aP.comp sh.adjunction) aQ sh.beta.inv) ≫
        conjugateEquiv (aQ.comp sY.adjunction) ay sY.beta.inv := by
  apply sheaf_trans_ext (coherentTopology Profinite.{u})
  intro G S
  exact coefficient_right_mates_app Λ f sX sY sh G S

private lemma coefficient_naturality
    (Λ : Profinite.CondensedRing.{u}) {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (sX : Corner Λ X) (sY : Corner Λ Y)
    (sh : Slice Λ (affineComponentMap f))
    (M : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (upperStar Ab.{u + 1} f).map (sX.beta.hom.app M) ≫
        (upperStarFromPointComp f).hom.app M =
      (abelianComparison Λ f sX sY sh).hom.app
          (((coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
            (affineComponentSpace X)).obj M) ≫
        sY.inverse.map (sh.beta.hom.app M) ≫ sY.beta.hom.app M := by
  let P := affineComponentSpace X
  let Q := affineComponentSpace Y
  let aP := slicePointAdjunction P
  let aQ := slicePointAdjunction Q
  let af := upperStarLowerStarAdjunction Ab.{u + 1} f
  let ax := absoluteAdjunction X
  let ay := absoluteAdjunction Y
  let a := abelianComparison Λ f sX sY sh
  have ha : conjugateEquiv (sX.adjunction.comp af)
      (sh.adjunction.comp sY.adjunction) a.inv = (directComparison Λ f sX sY).inv :=
    conjugateIso_symm_inv _ _ (directComparison Λ f sX sY)
  have hn := coefficient_right_mates Λ f sX sY sh
  have he := beta_pasting aP aQ sX.adjunction sY.adjunction sh.adjunction af ax ay
    sX.beta sY.beta sh.beta a (upperStarFromPointComp f) (by rw [ha]; exact hn)
  exact congr_app he M

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
