/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness

/-! # The shifted-line coordinate square -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

/-- The first projection square, with its morphisms reduced to pullback projections.
Source: the product-map construction (auxiliary; not a blueprint node). -/
theorem firstProjectionSquare
    {S X : Scheme.{u}} (f : X ⟶ S)
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :
    IsPullback (productMap f i hi) (pullback.fst f f)
      (projectiveLineDiagonalProjection S false) i.hom := by
  simpa only [projection] using projectionSquare f i hi false

section LineComparisons

attribute [local instance 2000] Abelian.toPreadditive

private theorem pullback_additive (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).Additive := by
  infer_instance

private theorem pullback_limits (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (upperStar (ModuleCat.{u + 1} A) f) := by
  infer_instance

private theorem pullback_colimits (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (upperStar (ModuleCat.{u + 1} A) f) := by
  infer_instance

attribute [local instance] pullback_additive pullback_limits pullback_colimits

attribute [local irreducible] upperStar lowerStar Scheme.finiteEtaleTateLine
  DerivedCategory.singleFunctors
  ordinaryFiniteSinglePullbackIso
  ordinaryFiniteSingleExactPullbackIso

attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor

private theorem line_comp (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    (t.line fg hZ).hom =
      (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) f).map (t.line g hZ).hom ≫
          (t.line f hY).hom := by
  subst fg
  by_cases hN : N = 0
  · subst N
    have hsub : Subsingleton Γ(Z, ⊤) :=
      subsingleton_of_zero_eq_one (isUnit_zero_iff.mp (by simpa using hZ))
    let : IsEmpty Z := Scheme.isEmpty_of_subsingleton_Γ hsub
    let : IsEmpty X := ⟨fun x ↦ isEmptyElim ((f ≫ g).base x)⟩
    exact (Scheme.Etale.isZero_sheaf_of_isEmpty
      (X.finiteEtaleTateLine 0 A hA)).eq_of_tgt _ _
  let d := Scheme.finiteEtaleTwistPullbackData A N (Nat.pos_of_ne_zero hN) hA
  let t' : OrdinaryFiniteTwistTransport A N hA := {
    roots := d.r
    line := fun v hT ↦ d.c v hT
      ((map_natCast v.appTop.hom N) ▸ hT.map v.appTop.hom) 1
    roots_normalization := d.laws.2.1
    line_normalization := fun v hT ↦ d.laws.2.2.1 v hT _ }
  have ht := ordinaryFiniteTwistTransport_unique A N hA t t'
  subst t
  exact congrArg Iso.hom (d.laws.2.2.2.2.2.2.2.1 g f hZ hY
    ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) 1)

/-- Cache the unshifted comparison before specializing the categories. -/
@[irreducible] private def singleComparisonHom
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    (F : C ⥤ D) (single : C₀ ⥤ C) (single' : D₀ ⥤ D) (pull : C₀ ⥤ D₀)
    (s : single ⋙ F ≅ pull ⋙ single') (K : C₀) (M : D₀) (a : pull.obj K ≅ M) :
    F.obj (single.obj K) ⟶ single'.obj M :=
  s.hom.app K ≫ single'.map a.hom

/-- Cache shifting a morphism before specializing the categories. -/
@[irreducible] private def shiftedHom
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K : C} {M : D} (a : F.obj K ⟶ M) (n : ℤ) :
    F.obj (K⟦n⟧) ⟶ M⟦n⟧ :=
  (F.commShiftIso n).hom.app K ≫ a⟦n⟧'

/-- The exact degree-zero comparison through the cached embeddings. -/
@[irreducible] private def exactLine₀ (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :=
  singleComparisonHom (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (upperStar (ModuleCat.{u + 1} A) f) (ordinaryFiniteSingleExactPullbackIso A f) K M a

/-- Shift the exact comparison while retaining the ordinary object interface. -/
@[irreducible] private def exactLine (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :=
  shiftedHom (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (exactLine₀ A f a) (2 : ℤ)

private theorem compared_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ] {K : C} {M : D}
    (a : G.obj K ⟶ M) (n : ℤ) :
    (F.commShiftIso n).hom.app K ≫ (e.hom.app K ≫ a)⟦n⟧' =
      e.hom.app (K⟦n⟧) ≫ shiftedHom G a n := by
  simp only [shiftedHom, Functor.map_comp]
  rw [NatTrans.shift_app_comm_assoc]

private theorem compared_shift_iso
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ]
    (single : C₀ ⥤ C) (single' : D₀ ⥤ D) (pull : C₀ ⥤ D₀)
    (s : single ⋙ G ≅ pull ⋙ single') (K : C₀) (M : D₀)
    (a : pull.obj K ≅ M) (n : ℤ) :
    ((F.commShiftIso n).app (single.obj K) ≪≫
      (shiftFunctor D n).mapIso
        ((Functor.isoWhiskerLeft single e ≪≫ s).app K ≪≫ single'.mapIso a)).hom =
      e.hom.app ((single.obj K)⟦n⟧) ≫
        shiftedHom G (singleComparisonHom G single single' pull s K M a) n := by
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app]
  simp only [Category.assoc]
  unfold singleComparisonHom
  exact compared_shift e _ n

private theorem singleComparison_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSinglePullbackIso A f =
      Functor.isoWhiskerLeft (ordinaryFiniteSingleFunctor A Y)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
      ordinaryFiniteSingleExactPullbackIso A f := by
  unfold ordinaryFiniteSinglePullbackIso
  rfl

private theorem shiftedSingle_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj K ≅ M) :
    letI : (ordinaryFinitePullback A f).CommShift ℤ :=
      commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
    (((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).app
        (ordinaryFiniteDegreeZero A Y K) ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((ordinaryFiniteSinglePullbackIso A f).app K ≪≫
          (ordinaryFiniteSingleFunctor A X).mapIso a)).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        ((ordinaryFiniteDegreeZero A Y K)⟦(2 : ℤ)⟧) ≫ exactLine A f a := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ℤ
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom ℤ :=
    NatTrans.CommShift.of_iso_inv
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm ℤ
  unfold exactLine exactLine₀
  rw [singleComparison_eq]
  exact compared_shift_iso
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (upperStar (ModuleCat.{u + 1} A) f) (ordinaryFiniteSingleExactPullbackIso A f)
    K M a (2 : ℤ)

private theorem shiftedLine_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app _ ≫
        exactLine A f (t.line f hY) := by
  unfold ordinaryFiniteShiftedLinePullback
  exact shiftedSingle_eq A f (t.line f hY)

private theorem raw_single_coherence
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G) :
    Functor.whiskerLeft (DerivedCategory.singleFunctor C 0)
        (Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso F G).symm).hom ≫
      Functor.whiskerRight (F.mapDerivedCategorySingleFunctor 0).hom G.mapDerivedCategory ≫
      Functor.whiskerLeft F (G.mapDerivedCategorySingleFunctor 0).hom =
      (H.mapDerivedCategorySingleFunctor 0).hom ≫
        Functor.whiskerRight e.hom (DerivedCategory.singleFunctor E 0) := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Category.assoc]
  exact Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor F G H e K

private theorem singleComparisonHom_comp
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (DF : D₀ ⥤ D₁) (DG : D₁ ⥤ D₂) (DH : D₀ ⥤ D₂)
    (e : H ≅ F ⋙ G) (de : DH ≅ DF ⋙ DG)
    (sF : S₀ ⋙ DF ≅ F ⋙ S₁) (sG : S₁ ⋙ DG ≅ G ⋙ S₂)
    (sH : S₀ ⋙ DH ≅ H ⋙ S₂)
    (hc : Functor.whiskerLeft S₀ de.hom ≫
        Functor.whiskerRight sF.hom DG ≫ Functor.whiskerLeft F sG.hom =
      sH.hom ≫ Functor.whiskerRight e.hom S₂)
    {K : C₀} {L : C₁} {M : C₂}
    (a : F.obj K ≅ L) (b : G.obj L ≅ M) (d : H.obj K ≅ M)
    (h : e.hom.app K ≫ G.map a.hom ≫ b.hom = d.hom) :
    de.hom.app (S₀.obj K) ≫
        DG.map (singleComparisonHom DF S₀ S₁ F sF K L a) ≫
          singleComparisonHom DG S₁ S₂ G sG L M b =
      singleComparisonHom DH S₀ S₂ H sH K M d := by
  unfold singleComparisonHom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := sG.hom.naturality a.hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hc' := congr_app hc K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc'
  rw [reassoc_of% hc']
  rw [← Functor.map_comp, ← Functor.map_comp, h]

private theorem raw_comparison_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : H ≅ F ⋙ G)
    {K : C} {L : D} {M : E} (a : F.obj K ≅ L) (b : G.obj L ≅ M)
    (d : H.obj K ≅ M) (h : e.hom.app K ≫ G.map a.hom ≫ b.hom = d.hom) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
          ((DerivedCategory.singleFunctor C 0).obj K) ≫
      G.mapDerivedCategory.map
        (singleComparisonHom F.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
          (DerivedCategory.singleFunctor D 0) F (F.mapDerivedCategorySingleFunctor 0) K L a) ≫
      singleComparisonHom G.mapDerivedCategory (DerivedCategory.singleFunctor D 0)
        (DerivedCategory.singleFunctor E 0) G (G.mapDerivedCategorySingleFunctor 0) L M b =
      singleComparisonHom H.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
        (DerivedCategory.singleFunctor E 0) H (H.mapDerivedCategorySingleFunctor 0) K M d := by
  exact singleComparisonHom_comp
    (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor D 0)
    (DerivedCategory.singleFunctor E 0) F G H _ _ _ e _
    (F.mapDerivedCategorySingleFunctor 0) (G.mapDerivedCategorySingleFunctor 0)
    (H.mapDerivedCategorySingleFunctor 0) (raw_single_coherence F G H e) a b d h

private theorem exactLine₀_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    {K : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) g).obj K ≅ L)
    (b : (upperStar (ModuleCat.{u + 1} A) f).obj L ≅ M)
    (d : (upperStar (ModuleCat.{u + 1} A) fg).obj K ≅ M)
    (h : (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app K ≫
      (upperStar (ModuleCat.{u + 1} A) f).map a.hom ≫ b.hom = d.hom) :
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app (ordinaryFiniteDegreeZero A Z K) ≫
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
          (exactLine₀ A g a) ≫ exactLine₀ A f b = exactLine₀ A fg d := by
  unfold exactLine₀ ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
    ordinaryFiniteSingleExactPullbackIso
  exact raw_comparison_comp
    (upperStar (ModuleCat.{u + 1} A) g) (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} A) fg)
    (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) a b d h

private theorem shift_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (e : H ≅ F ⋙ G) [NatTrans.CommShift e.hom ℤ]
    {K : C} {L : D} {M : E} (a : F.obj K ⟶ L) (b : G.obj L ⟶ M)
    (d : H.obj K ⟶ M) (h : e.hom.app K ≫ G.map a ≫ b = d) (n : ℤ) :
    e.hom.app (K⟦n⟧) ≫ G.map ((F.commShiftIso n).hom.app K ≫ a⟦n⟧') ≫
        (G.commShiftIso n).hom.app L ≫ b⟦n⟧' =
      (H.commShiftIso n).hom.app K ≫ d⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]
  have he := NatTrans.shift_app_comm e.hom n K
  simp only [Functor.commShiftIso_comp_hom_app] at he
  rw [← reassoc_of% he]
  simp only [← Functor.map_comp, h]

private theorem compared_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H') (c : H' ≅ F' ⋙ G')
    {K : C} {B : D} {V : E} (a : F'.obj K ⟶ B) (b : G'.obj B ⟶ V)
    (d : H'.obj K ⟶ V) (hc : c.hom.app K ≫ G'.map a ≫ b = d) :
    (eH ≪≫ c ≪≫ Functor.isoWhiskerRight eF.symm G' ≪≫
        Functor.isoWhiskerLeft F eG.symm).hom.app K ≫
      G.map (eF.hom.app K ≫ a) ≫ eG.hom.app B ≫ b = eH.hom.app K ≫ d := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  rw [← eG.inv.naturality_assoc]
  rw [← G'.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hc]

private theorem shiftedLine_comp
    (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app
        ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A f).map (ordinaryFiniteShiftedLinePullback A N hA t g hZ).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
      (ordinaryFiniteShiftedLinePullback A N hA t fg hZ).hom := by
  let c := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have hc₀ := exactLine₀_comp A f g fg hfg
    (t.line g hZ) (t.line f hY) (t.line fg hZ)
    (line_comp A N hA t f g hZ hY fg hfg).symm
  have : NatTrans.CommShift c.hom ℤ := by
    dsimp only [c, Iso.trans_hom]
    infer_instance
  have hc := shift_composite
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory c
    (exactLine₀ A g (t.line g hZ)) (exactLine₀ A f (t.line f hY))
    (exactLine₀ A fg (t.line fg hZ)) hc₀ (2 : ℤ)
  have hc' : c.hom.app ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
      (exactLine A g (t.line g hZ)) ≫ exactLine A f (t.line f hY) =
    exactLine A fg (t.line fg hZ) := by
    simpa only [exactLine, shiftedHom, ordinaryFiniteLine, ordinaryFiniteDegreeZero,
      ordinaryFiniteSingleFunctor_eq, Category.assoc] using hc
  dsimp only [ordinaryFiniteLine, ordinaryFiniteDegreeZero] at hc'
  have h := compared_composite
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) fg) c
    (exactLine A g (t.line g hZ)) (exactLine A f (t.line f hY))
    (exactLine A fg (t.line fg hZ)) hc'
  dsimp only [ordinaryFinitePullback, ordinaryFiniteLine, ordinaryFiniteSingleFunctor,
    ordinaryFiniteDegreeZero] at h ⊢
  simp (config := { dsimp := false }) only [shiftedLine_eq, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, c, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc] at h ⊢
  exact h

end LineComparisons

private theorem square_line
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {W X Y Z : Scheme.{u}} {a : W ⟶ X} {b : W ⟶ Y} {p : X ⟶ Z} {e : Y ⟶ Z}
    (sq : CommSq a b p e) (hZ : IsUnit (N : Γ(Z, ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A a).map
        (ordinaryFiniteShiftedLinePullback A N hA t p hZ).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t a hX).hom =
    (ordinaryFinitePullback A b).map
        (ordinaryFiniteShiftedLinePullback A N hA t e hZ).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t b hY).hom := by
  have h₁ := shiftedLine_comp A N hA t a p hZ hX (a ≫ p) rfl
  have h₂ := shiftedLine_comp A N hA t b e hZ hY (a ≫ p) sq.w
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    b e (a ≫ p) sq.w).hom.app _)).mp
  simpa only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc] using h₁.trans h₂.symm

/-- The coefficient square for the two pulled-back coordinates, without any
direct image, exchange map, or trace.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the equality p1* q*=p2* q* in the second triangle.
(auxiliary; not a blueprint node)

Proof: expand coefficientComparison and SfDiagonalKernel.coordinate. The roots
inclusion and pure coefficient generators uniquely characterize normalized line
transport. Thus for composable morphisms its comparison is the composite of
the two comparisons and upperStarComp. For N>0 this is also the composition law
of finiteEtaleTwistPullbackData; for N=0 the invertibility hypothesis makes S
empty, and maps to the line sheaf are unique. Apply the degree-zero functor,
its canonical exact/left-derived comparison, and shift by two. Naturality of
these comparisons gives the same composition law for shifted lines. Apply it
to productMap followed by the first projective projection and to the first
projection followed by i, which are equal by projectionSquare. Apply it again
to the two projections followed by f. The latter equality is pullback.condition;
its derived comparison is CoordinateTrace.coordinate. Cancel the normalized
line isomorphisms, leaving the displayed square. This proof applies to arbitrary
schemes and zero coefficient rings and introduces no integration identity. -/
theorem coordinateLineComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) :
    (coefficientComparison A N hA t f i hi hS).inv ≫
        (ordinaryFinitePullback A (productMap f i hi)).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (projectiveLineDiagonalProjection S false)
            (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (firstProjectionSquare f i hi).toCommSq).inv.app
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) =
      (SfDiagonalKernel.coordinate A f
        (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1)
        (ordinaryFiniteShiftedLinePullback A N hA t f hS).symm).inv ≫
      (ordinaryFinitePullback A (pullback.fst f f)).map
        (ordinaryFiniteShiftedLinePullback A N hA t i.hom
          (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv := by
  let hP := finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS
  let hX := finiteP1_unitOnPullback N f hS
  let hW := finiteP1_unitOnPullback N
    ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
      (ProjectiveLine S ↘ S)) hS
  let B := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  let v := ordinaryFiniteShiftedLinePullback A N hA t
    (projectiveLineDiagonalProjection S false) hP
  let l := ordinaryFiniteShiftedLinePullback A N hA t i.hom hP
  let c := ordinaryFiniteShiftedLinePullback A N hA t (productMap f i hi) hW
  let c₁ := ordinaryFiniteShiftedLinePullback A N hA t (pullback.fst f f) hX
  let c₂ := ordinaryFiniteShiftedLinePullback A N hA t (pullback.snd f f) hX
  let k := SfDiagonalKernel.coordinate A f
    (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1)
    (ordinaryFiniteShiftedLinePullback A N hA t f hS).symm
  let s := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
    (firstProjectionSquare f i hi).toCommSq).app B
  have hs : s ≪≫ (ordinaryFinitePullback A (productMap f i hi)).mapIso v ≪≫ c =
      (ordinaryFinitePullback A (pullback.fst f f)).mapIso l ≪≫ c₁ := by
    apply Iso.ext
    exact square_line A N hA t (firstProjectionSquare f i hi).toCommSq hP hW hX
  have hs' := congrArg Iso.inv hs
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc] at hs'
  have hk : k.hom ≫ c₂.hom = c₁.hom := by
    have h := square_line A N hA t
      (CommSq.mk (pullback.condition (f := f) (g := f)).symm) hS hX hX
    dsimp only [k, SfDiagonalKernel.coordinate, CoordinateTrace.coordinate]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.symm_inv,
      Category.assoc]
    change (ordinaryFinitePullback A (pullback.fst f f)).map
        (ordinaryFiniteShiftedLinePullback A N hA t f hS).inv ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom.app
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A (pullback.snd f f)).map
        (ordinaryFiniteShiftedLinePullback A N hA t f hS).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t (pullback.snd f f) hX).hom = _
    rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hk' : c₂.hom ≫ c₁.inv = k.inv := by
    apply (cancel_epi k.hom).mp
    rw [← Category.assoc, hk, Iso.hom_inv_id, Iso.hom_inv_id]
  unfold coefficientComparison
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
  change c₂.hom ≫ c.inv ≫ _ ≫ s.inv = k.inv ≫ _
  rw [hs', ← Category.assoc, hk']

end AlgebraicGeometry.Etale.SfP1Transport
