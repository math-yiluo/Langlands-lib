/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! Restriction of scalars and ordinary inverse-image composition.

## References

* Stacks, Modules on Sites, Tags 03D8 and 03D7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Functor

/-- Ordinary scalar restriction in constant-ring coordinates. -/
abbrev ordinaryScalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (Scheme.proEtaleConstantRingMap (T := T) φ)

/-- The recorded ordinary constant-ring inverse image. -/
abbrev ordinaryConstantPullback (A : Type u) [CommRing A] {V W : Scheme.{u}} (f : V ⟶ W) :=
  StrictTower.modulePullback (ULift.{u + 1, u} A) f

private abbrev push (A : Type u) [CommRing A] {V W : Scheme.{u}} (f : V ⟶ W) :=
  StrictTower.moduleDirectImage (ULift.{u + 1, u} A) f

private abbrev padj (A : Type u) [CommRing A] {V W : Scheme.{u}} (f : V ⟶ W) :=
  Scheme.proEtaleRingModuleAdjunction f (Scheme.proEtaleConstantRing W A)
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRingComparison f A)

/-- Constant coefficient maps commute with inverse-image identification. -/
theorem coeffSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (f : V ⟶ W) :
    (Scheme.proEtaleConstantRingComparison f A).hom ≫
        Scheme.proEtaleConstantRingMap (T := V) φ =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (Scheme.proEtaleConstantRingMap (T := W) φ) ≫
        (Scheme.proEtaleConstantRingComparison f B).hom := by
  simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (a := CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The specified ordinary restriction/pullback mate. -/
def ordinaryRestrictionComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (f : V ⟶ W) :
    ordinaryScalarRestriction φ W ⋙ ordinaryConstantPullback A f ⟶
      ordinaryConstantPullback B f ⋙ ordinaryScalarRestriction φ V :=
  Scheme.proEtaleRingRestrictionPullbackInv f
    (Scheme.proEtaleConstantRing W A) (Scheme.proEtaleConstantRing W B)
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRingMap (T := W) φ)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B) (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality f
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)

private def directComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (f : V ⟶ W) :=
  Scheme.proEtaleRingRestrictionDirectImage f
    (Scheme.proEtaleConstantRing W A) (Scheme.proEtaleConstantRing W B)
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRingMap (T := W) φ)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B) (coeffSquare φ f)

private lemma directComparison_apply {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (f : V ⟶ W)
    (N : Scheme.proEtaleRingModules V (Scheme.proEtaleConstantRing V B))
    (Y : W.ProEtᵒᵖ)
    (n : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj Y)) :
    ((directComparison φ f).hom.app N).val.app Y n = n :=
  (Classical.choose_spec (Scheme.proEtaleRingRestrictionDirectImage_existsUnique
    f (Scheme.proEtaleConstantRing W A) (Scheme.proEtaleConstantRing W B)
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRingMap (T := W) φ)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B) (coeffSquare φ f))).1 N Y n

private lemma rcomp_apply (A : Type u) [CommRing A]
    {V W Z : Scheme.{u}} (f : V ⟶ W) (g : W ⟶ Z)
    (N : Scheme.proEtaleRingModules V (Scheme.proEtaleConstantRing V A))
    (Y : Z.ProEt)
    (n : ((push A f ⋙ push A g).obj N).val.obj (Opposite.op Y)) :
    ((StrictTower.moduleRComp (ULift.{u + 1, u} A) f g).hom.app N).val.app
        (Opposite.op Y) n =
      N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app Y).op n :=
  (Classical.choose_spec (StrictTower.moduleRComp_existsUnique
    (ULift.{u + 1, u} A) f g)).1 N Y n

private lemma comparison_mate {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (f : V ⟶ W) :
    mateEquiv (padj B f) (padj A f) (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison φ f)) =
      TwoSquare.mk _ _ _ _ (directComparison φ f).hom := by
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [mateEquiv_symm_apply, ordinaryRestrictionComparison,
    Scheme.proEtaleRingRestrictionPullbackInv, Scheme.proEtaleRingRestrictionPullbackApp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_map, Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  exact (Category.comp_id _).symm

private lemma mateSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

-- Keep inverse-image constructions folded during the compositor calculations.
attribute [local irreducible] Scheme.proEtaleRingModulePullback

private lemma comparison_comp {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W Z : Scheme.{u}} (f : V ⟶ W) (g : W ⟶ Z)
    (M : Scheme.proEtaleRingModules Z (Scheme.proEtaleConstantRing Z B)) :
    (StrictTower.moduleGComp (ULift.{u + 1, u} A) f g).hom.app
        ((ordinaryScalarRestriction φ Z).obj M) ≫
        (ordinaryConstantPullback A f).map ((ordinaryRestrictionComparison φ g).app M) ≫
        (ordinaryRestrictionComparison φ f).app ((ordinaryConstantPullback B g).obj M) =
      (ordinaryRestrictionComparison φ (f ≫ g)).app M ≫
        (ordinaryScalarRestriction φ V).map
          ((StrictTower.moduleGComp (ULift.{u + 1, u} B) f g).hom.app M) := by
  let q := (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison φ g)).vComp
    (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison φ f))
  have h := mateSquare ((padj B g).comp (padj B f)) (padj B (f ≫ g))
    ((padj A g).comp (padj A f)) (padj A (f ≫ g)) q
    (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison φ (f ≫ g)))
    (StrictTower.moduleGComp (ULift.{u + 1, u} A) f g).hom
    (StrictTower.moduleGComp (ULift.{u + 1, u} B) f g).hom
  have hc : q.whiskerRight
      (StrictTower.moduleGComp (ULift.{u + 1, u} A) f g).hom =
      (TwoSquare.mk _ _ _ _ (ordinaryRestrictionComparison φ (f ≫ g))).whiskerLeft
        (StrictTower.moduleGComp (ULift.{u + 1, u} B) f g).hom := by
    apply h
    dsimp only [q]
    rw [mateEquiv_hcomp, comparison_mate, comparison_mate, comparison_mate]
    have hG (C : Type u) [CommRing C] :
        conjugateEquiv ((padj C g).comp (padj C f)) (padj C (f ≫ g))
            (StrictTower.moduleGComp (ULift.{u + 1, u} C) f g).hom =
          (StrictTower.moduleRComp (ULift.{u + 1, u} C) f g).hom :=
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
    rw [hG A, hG B]
    refine NatTrans.ext (funext fun N ↦ ?_)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app]
    simp only [ModuleCat.comp_apply]
    erw [directComparison_apply φ g ((push B f).obj N) Y n]
    change ((StrictTower.moduleRComp (ULift.{u + 1, u} A) f g).hom.app
        ((ordinaryScalarRestriction φ V).obj N)).val.app Y
          (((directComparison φ f).hom.app N).val.app
            ((Scheme.proEtaleBaseChange g).op.obj Y) n) =
      ((directComparison φ (f ≫ g)).hom.app N).val.app Y
        (((StrictTower.moduleRComp (ULift.{u + 1, u} B) f g).hom.app N).val.app Y n)
    erw [directComparison_apply φ f N ((Scheme.proEtaleBaseChange g).op.obj Y) n,
      directComparison_apply φ (f ≫ g) N Y _]
    obtain ⟨Y⟩ := Y
    erw [rcomp_apply A f g ((ordinaryScalarRestriction φ V).obj N) Y n, rcomp_apply B f g N Y n]
    rfl
  have hm := congrArg (fun z ↦ z.app M) hc
  simpa only [q, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, ordinaryConstantPullback, ordinaryScalarRestriction,
    StrictTower.modulePullback,
    StrictTower.constantRingIso, Scheme.proEtaleConstantRingComparison] using hm

private lemma pasteTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {α : Sort*} (P : α → C ⥤ D) (Q : α → E ⥤ F)
    (R : E ⥤ C) (S : F ⥤ D) (q : ∀ x, R ⋙ P x ⟶ Q x ⋙ S)
    {x y : α} (h : x = y)
    {P₁ P₂ : C ⥤ D} {Q₁ Q₂ : E ⥤ F}
    (a : P x ≅ P₁) (a' : P y ≅ P₂)
    (b : Q x ≅ Q₁) (b' : Q y ≅ Q₂)
    {T₁ T₂ : E ⥤ D}
    (p : R ⋙ P₁ ⟶ T₁) (r : T₁ ⟶ Q₁ ⋙ S)
    (p' : R ⋙ P₂ ⟶ T₂) (r' : T₂ ⟶ Q₂ ⋙ S)
    (ha : ∀ M, a.hom.app (R.obj M) ≫ p.app M ≫ r.app M =
      (q x).app M ≫ S.map (b.hom.app M))
    (ha' : ∀ M, a'.hom.app (R.obj M) ≫ p'.app M ≫ r'.app M =
      (q y).app M ≫ S.map (b'.hom.app M))
    (z : P₂ ≅ P₁) (w : Q₂ ≅ Q₁)
    (hz : z = a'.symm ≪≫ eqToIso (congrArg P h.symm) ≪≫ a)
    (hw : w = b'.symm ≪≫ eqToIso (congrArg Q h.symm) ≪≫ b) (M : E) :
    z.inv.app (R.obj M) ≫ p'.app M ≫ r'.app M =
      p.app M ≫ r.app M ≫ S.map (w.inv.app M) := by
  rw [hz, hw]
  subst y
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app]
  apply (cancel_epi (a.hom.app (R.obj M))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [ha', reassoc_of% (ha M)]
  have hb : S.map (b.hom.app M) ≫ S.map (b.inv.app M) = 𝟙 _ := by
    rw [← S.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% hb]

/-- Restriction of scalars respects the specified ordinary pullback-square compositor.
No derived tensor functor, localization, or extension by zero occurs here. -/
theorem ordinaryRestrictionPullbackSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : OpenImmersionSquare gU j' j g)
    (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X B)) :
    (StrictTower.moduleSquareG (ULift.{u + 1, u} A) gU j' j g sq.toCommSq.w).inv.app
        ((ordinaryScalarRestriction φ X).obj M) ≫
      (ordinaryConstantPullback A j').map ((ordinaryRestrictionComparison φ g).app M) ≫
        (ordinaryRestrictionComparison φ j').app ((ordinaryConstantPullback B g).obj M) =
      (ordinaryConstantPullback A gU).map ((ordinaryRestrictionComparison φ j).app M) ≫
        (ordinaryRestrictionComparison φ gU).app ((ordinaryConstantPullback B j).obj M) ≫
        (ordinaryScalarRestriction φ U').map
          ((StrictTower.moduleSquareG (ULift.{u + 1, u} B) gU j' j g sq.toCommSq.w).inv.app M) := by
  exact pasteTransport (fun f ↦ StrictTower.modulePullback (ULift.{u + 1, u} A) f)
    (fun f ↦ StrictTower.modulePullback (ULift.{u + 1, u} B) f)
    (ordinaryScalarRestriction φ X) (ordinaryScalarRestriction φ U')
    (fun f ↦ ordinaryRestrictionComparison φ f) sq.toCommSq.w
    (StrictTower.moduleGComp (ULift.{u + 1, u} A) gU j)
    (StrictTower.moduleGComp (ULift.{u + 1, u} A) j' g)
    (StrictTower.moduleGComp (ULift.{u + 1, u} B) gU j)
    (StrictTower.moduleGComp (ULift.{u + 1, u} B) j' g)
    (Functor.whiskerRight (ordinaryRestrictionComparison φ j) (ordinaryConstantPullback A gU))
    (Functor.whiskerLeft (ordinaryConstantPullback B j) (ordinaryRestrictionComparison φ gU))
    (Functor.whiskerRight (ordinaryRestrictionComparison φ g) (ordinaryConstantPullback A j'))
    (Functor.whiskerLeft (ordinaryConstantPullback B g) (ordinaryRestrictionComparison φ j'))
    (comparison_comp φ gU j) (comparison_comp φ j' g)
    (StrictTower.moduleSquareG (ULift.{u + 1, u} A) gU j' j g sq.toCommSq.w)
    (StrictTower.moduleSquareG (ULift.{u + 1, u} B) gU j' j g sq.toCommSq.w)
    (StrictTower.moduleSquareG_eq _ _ _ _ _ _)
    (StrictTower.moduleSquareG_eq _ _ _ _ _ _) M

end AlgebraicGeometry.ProEtale
