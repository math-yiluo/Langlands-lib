/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! Tensor/pullback compatibility for an arbitrary Cartesian square.
Source: Stacks, Modules on Sites, Tags 03D8 and 03D7, and sites-cohomology,
Tags 0D6D and 0E47 (blueprint: lem-sp-scalar-tensor-pullback-square).
The ordinary composition and localization calculations adapt the proved helpers of
OrdinaryRestrictionPullbackSquare and TensorPullbackSquare; only the square equality
is needed, so no open-immersion hypothesis enters.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Avoid replaying expensive sectionwise transport tactics for linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DirectScalar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Functor

/-- Ordinary scalar restriction in constant-ring coordinates.
Source: Stacks Tag 03D7 (blueprint: lem-fix-ordinary-restriction-pullback-square). -/
private abbrev ordinaryScalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (Scheme.proEtaleConstantRingMap (T := T) φ)

/-- The recorded ordinary constant-ring inverse image.
Source: Stacks Tag 03D8 (blueprint: lem-fix-ordinary-restriction-pullback-square). -/
private abbrev ordinaryConstantPullback (A : Type u) [CommRing A] {V W : Scheme.{u}} (f : V ⟶ W) :=
  StrictTower.modulePullback (ULift.{u + 1, u} A) f

private abbrev push (A : Type u) [CommRing A] {V W : Scheme.{u}} (f : V ⟶ W) :=
  StrictTower.moduleDirectImage (ULift.{u + 1, u} A) f

private abbrev padj (A : Type u) [CommRing A] {V W : Scheme.{u}} (f : V ⟶ W) :=
  Scheme.proEtaleRingModuleAdjunction f (Scheme.proEtaleConstantRing W A)
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRingComparison f A)

/-- Constant coefficient maps commute with inverse-image identification.
Source: Stacks Tag 03D7 (blueprint: lem-fix-ordinary-restriction-pullback-square).
Proof: apply naturality of the canonical constant inverse-image map. -/
private theorem coeffSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V W : Scheme.{u}} (f : V ⟶ W) :
    (Scheme.proEtaleConstantRingComparison f A).hom ≫
        Scheme.proEtaleConstantRingMap (T := V) φ =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (Scheme.proEtaleConstantRingMap (T := W) φ) ≫
        (Scheme.proEtaleConstantRingComparison f B).hom := by
  simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (a := CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The specified ordinary restriction/pullback mate.
Source: Stacks Tag 03D7 (blueprint: lem-fix-ordinary-restriction-pullback-square). -/
private def ordinaryRestrictionComparison {A B : Type u} [CommRing A] [CommRing B]
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
attribute [local irreducible] Scheme.completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Scheme.proEtaleRingModulePullback

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
    Category.comp_id, Category.assoc] using hm

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
No derived tensor functor, localization, or extension by zero occurs here.
Source: Stacks, Modules on Sites, Tags 03D8 and 03D7; the ordinary composition
calculation underlying parent `lem-fix-tensor-pullback-square`.
(blueprint: lem-fix-ordinary-restriction-pullback-square)
Proof: first use the fibre-product direct-image compositor moduleRComp. Its forward
map is restriction along Over.pullbackComp.hom, by moduleRComp_existsUnique.
Restriction of scalars leaves sections and their restriction maps unchanged.
The canonical restriction/direct-image comparison is the identity on every section,
by proEtaleRingRestrictionDirectImage_existsUnique. Thus the two pastings involving
the direct-image compositor and these comparisons agree sectionwise. Conjugate this
identity by the two composite module adjunctions. The conjugate of moduleRComp is
moduleGComp.inv by leftAdjointCompIso, and the inverse mate of the sectionwise
identity is proEtaleRingRestrictionPullbackInv by its defining unit-counit formula.
The mate pasting laws give compatibility of these inverse-image comparisons with
moduleGComp. Apply it to both composable paths in the square. Eliminate their common
composite using sq.toCommSq.w; equality transport is natural in the coefficient map.
Composing one path with the inverse of the other gives precisely moduleSquareG.inv
on each coefficient ring and the displayed equation. The computation is valid for
empty schemes, the zero ring, and arbitrary coefficient homomorphisms. -/
private theorem ordinaryRestrictionPullbackSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : ChosenCartesianSquare gU j' j g)
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

local notation "CR" => Scheme.proEtaleConstantRing
local notation "PB" => Scheme.proEtaleConstantRingDerivedPullback
local notation "CC" => Scheme.proEtaleConstantRingComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ M, c.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.app M))
    (N : C₀) :
    S₃.map (c.app N) ≫
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).app (G.obj N) ≫
        I'.map (((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).app N) =
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).app (J.obj N) ≫
        H'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).app N) ≫
        d.app (S₀.obj N) := by
  let lJ := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ))
  let lH := ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH))
  let lG := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG))
  let lI := ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI))
  have hj (K : C₀) : J.map (a₀.unit.app K) ≫ qJ.app (S₀.obj K) =
      a₁.unit.app (J.obj K) ≫ R₁.map (lJ.app K) :=
    unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qJ) K
  have hh (K : C₁) : H.map (a₁.unit.app K) ≫ qH.app (S₁.obj K) =
      a₃.unit.app (H.obj K) ≫ R₃.map (lH.app K) :=
    unit_mateEquiv_symm a₁ a₃ (TwoSquare.mk _ _ _ _ qH) K
  have hg (K : C₀) : G.map (a₀.unit.app K) ≫ qG.app (S₀.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (lG.app K) :=
    unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qG) K
  have hi (K : C₂) : I.map (a₂.unit.app K) ≫ qI.app (S₂.obj K) =
      a₃.unit.app (I.obj K) ≫ R₃.map (lI.app K) :=
    unit_mateEquiv_symm a₂ a₃ (TwoSquare.mk _ _ _ _ qI) K
  change S₃.map (c.app N) ≫ lI.app (G.obj N) ≫ I'.map (lG.app N) =
    lH.app (J.obj N) ≫ H'.map (lJ.app N) ≫ d.app (S₀.obj N)
  apply (a₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := a₃.unit.naturality (c.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← reassoc_of% (hi (G.obj N))]
  have hq := qI.naturality (lG.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← I.map_comp_assoc, ← hg, I.map_comp]
  have hcn := c.naturality (a₀.unit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcn
  simp only [Category.assoc, Functor.id_obj] at hcn ⊢
  rw [← reassoc_of% hcn, hc]
  rw [← reassoc_of% (hh (J.obj N))]
  have hqn := qH.naturality (lJ.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqn
  rw [← reassoc_of% hqn, ← H.map_comp_assoc, hj]
  simp only [Functor.map_comp, Category.assoc]

section ExactCoherence
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory F]
  (L : C ⥤ D) (M : D ⥤ E) (N : E ⥤ F)
  [L.Additive] [M.Additive] [N.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]

private noncomputable abbrev tripleComparison :
    (L ⋙ M ⋙ N).mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ M.mapDerivedCategory ⋙ N.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (L ⋙ M) N).symm ≪≫
    isoWhiskerRight (Functor.mapDerivedCategoryCompIso L M).symm N.mapDerivedCategory

private lemma tripleComparison_hom :
    (tripleComparison L M N).hom =
      (Functor.mapDerivedCategoryCompIso L (M ⋙ N)).inv ≫
        Functor.whiskerLeft L.mapDerivedCategory (Functor.mapDerivedCategoryCompIso M N).inv :=
  (Functor.mapDerivedCategoryCompIso_assoc L M N).symm

variable {L M N}
  {D' : Type*} [Category D'] [Abelian D'] [HasDerivedCategory D']
  {L' : C ⥤ D'} {M' : D' ⥤ E}
  [L'.Additive] [M'.Additive]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits M'] [PreservesFiniteColimits M']

private lemma tripleComparison_right (e : L ⋙ M ≅ L' ⋙ M') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso e).hom
          N.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerRight e N)).hom ≫
        (tripleComparison L' M' N).hom := by
  dsimp only [tripleComparison, Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Functor.whiskerRight_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerRight_comp
    (Functor.mapDerivedCategoryCompIso L M).inv
    (Functor.mapDerivedCategoryCompIso L M).hom N.mapDerivedCategory), Iso.inv_hom_id]
  simp only [Functor.whiskerRight_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e N)]

variable {E' : Type*} [Category E'] [Abelian E'] [HasDerivedCategory E']
  {M'' : D ⥤ E'} {N' : E' ⥤ F}
  [M''.Additive] [N'.Additive]
  [PreservesFiniteLimits M''] [PreservesFiniteColimits M'']
  [PreservesFiniteLimits N'] [PreservesFiniteColimits N']

private lemma tripleComparison_left (e : M ⋙ N ≅ M'' ⋙ N') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerLeft L.mapDerivedCategory
          (Functor.mapDerivedCategorySquareIso e).hom =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerLeft L e)).hom ≫
        (tripleComparison L M'' N').hom := by
  rw [tripleComparison_hom, tripleComparison_hom]
  dsimp only [Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerLeft_comp L.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso M N).inv
    (Functor.mapDerivedCategoryCompIso M N).hom), Iso.inv_hom_id]
  simp only [Functor.whiskerLeft_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft L e)]

end ExactCoherence

section DerivedCube
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']

private lemma derivedCube
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : ∀ M, c.hom.app (R₀.obj M) ≫ I.map (qG.hom.app M) ≫ qI.hom.app (G'.obj M) =
      H.map (qJ.hom.app M) ≫ qH.hom.app (J'.obj M) ≫ R₃.map (d.hom.app M))
    (M : DerivedCategory D₀) :
    (Functor.mapDerivedCategorySquareIso c).hom.app (R₀.mapDerivedCategory.obj M) ≫
        I.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qG).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qI).hom.app (G'.mapDerivedCategory.obj M) =
      H.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qJ).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qH).hom.app (J'.mapDerivedCategory.obj M) ≫
        R₃.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app M) := by
  let pL := isoWhiskerLeft R₀ c ≪≫ isoWhiskerRight qG I ≪≫ isoWhiskerLeft G' qI
  let pR := isoWhiskerRight qJ H ≪≫ isoWhiskerLeft J' qH ≪≫ isoWhiskerRight d R₃
  have hp : pL = pR := by
    apply Iso.ext
    ext K
    exact hc K
  have hL : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerLeft R₀.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom
        I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qI).hom =
      (Functor.mapDerivedCategoryNatIso pL).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_left c),
      reassoc_of% (tripleComparison_right qG), tripleComparison_left qI]
    simp only [pL, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have hR : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom
        H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom
        R₃.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso pR).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_right qJ),
      reassoc_of% (tripleComparison_left qH), tripleComparison_right d]
    simp only [pR, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have h := hL.trans ((congrArg (fun p ↦
    (Functor.mapDerivedCategoryNatIso p).hom ≫ (tripleComparison G' I' R₃).hom) hp).trans hR.symm)
  have h' := (cancel_epi (tripleComparison R₀ J H).hom).1 h
  exact congr_app h' M

end DerivedCube

/-- The tensor/pullback comparisons commute around a square, with its specified
inverse-image compositor. This involves no open extension and no base-change mate.
Source: Stacks Tags 07A4 and 0G7E; the tensor composition calculation in
`lem-fix-open-scalar-exchange`, proof step 2.
(blueprint: lem-sp-scalar-tensor-pullback-square)
Proof: ordinary restriction of scalars commutes with the specified pullback-square
compositor, by ordinaryRestrictionPullbackSquare. Exact derived-functor composition
coherence transports this ordinary cube through localization: the triple-comparison
associativity and whiskering identities identify both descended pastings. Apply the
four scalar extension/restriction adjunctions to this derived cube. Injectivity of the
last scalar Hom equivalence, the four mate-unit identities, and naturality give the
same cube for the left mates. By the definition of proEtaleReductionPullbackIso,
these left mates are the inverse tensor comparisons in the statement. The argument
includes empty schemes and zero coefficient rings and uses no flatness of B over A. -/
theorem scalarTensorPullbackSquare {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B)
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : ChosenCartesianSquare gU j' j g)
    (N : DerivedCategory (Scheme.proEtaleRingModules X (CR X A))) :
    let S (T : Scheme.{u}) := directImageScalarExtension φ T
    let c (R : Type u) [CommRing R] := Functor.mapDerivedCategorySquareIso
      (StrictTower.moduleSquareG (ULift.{u + 1, u} R) gU j' j g sq.toCommSq.w)
    let lam {V W : Scheme.{u}} (f : V ⟶ W) := directImageScalarPullbackIso φ f
    (S U').map ((c A).inv.app N) ≫
      (lam j').inv.app ((PB A g).obj N) ≫ (PB B j').map ((lam g).inv.app N) =
    (lam gU).inv.app ((PB A j).obj N) ≫
      (PB B gU).map ((lam j).inv.app N) ≫ (c B).inv.app ((S X).obj N) := by
  let R (T : Scheme.{u}) := Scheme.proEtaleRingRestrictScalars
    (Scheme.proEtaleConstantRingMap (T := T) φ)
  let P (R : Type u) [CommRing R] {V W : Scheme.{u}} (f : V ⟶ W) :=
    StrictTower.modulePullback (ULift.{u + 1, u} R) f
  let c (R : Type u) [CommRing R] :=
    StrictTower.moduleSquareG (ULift.{u + 1, u} R) gU j' j g sq.toCommSq.w
  let q {V W : Scheme.{u}} (f : V ⟶ W) :=
    Scheme.proEtaleRingRestrictionPullbackInv f
      (CR W A) (CR W B) (CR V A) (CR V B)
      (Scheme.proEtaleConstantRingMap (T := W) φ)
      (Scheme.proEtaleConstantRingMap (T := V) φ) (CC f A) (CC f B) (by
        simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
          (Scheme.proEtaleConstantInverseImageMap_naturality f
            (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)
  have hq {V W : Scheme.{u}} (f : V ⟶ W) : IsIso (q f) :=
    Scheme.proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  let qi {V W : Scheme.{u}} (f : V ⟶ W) := @asIso _ _ _ _ (q f) (hq f)
  have hc (M : DerivedCategory (Scheme.proEtaleRingModules X (CR X B))) :=
    derivedCube (qi j) (qi gU) (qi g) (qi j') (c A).symm (c B).symm
      (ordinaryRestrictionPullbackSquare φ gU j' j g sq) M
  let adj (T : Scheme.{u}) := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := T) φ)
  have hm := mateCube (adj X) (adj U) (adj X') (adj U')
    (Functor.mapDerivedCategorySquareIso (qi j)).hom
    (Functor.mapDerivedCategorySquareIso (qi gU)).hom
    (Functor.mapDerivedCategorySquareIso (qi g)).hom
    (Functor.mapDerivedCategorySquareIso (qi j')).hom
    (Functor.mapDerivedCategorySquareIso (c A).symm).hom
    (Functor.mapDerivedCategorySquareIso (c B).symm).hom hc N
  simpa only [directImageScalarPullbackIso, directImageScalarExtension,
    Scheme.proEtaleReductionPullbackIso, Scheme.proEtaleReductionPullbackInv,
    Scheme.proEtaleRingRestrictionDerivedPullback, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, Category.assoc,
    asIso_hom, qi, q, c, P, R, adj] using hm

end AlgebraicGeometry.ProEtale.DirectScalar
