/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness

/-! # Exchange for the twisted projective-line unit

Source: blueprint lemma-cohomology-projective-line-trace, base-change paragraph; the mate-unit
calculation in lem-sp-finite-p1-kummer-naturality, step 3.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000]
  DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

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

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  upperStar lowerStar Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Scheme.finiteEtaleTateLine
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  ordinaryFiniteSinglePullbackIso
  ordinaryFiniteSingleExactPullbackIso

attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor

private theorem line_comp (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    (t.line fg hZ).hom =
      (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) f).map (t.line g hZ).hom ≫
          (t.line f hY).hom := by
  subst fg
  let d := Scheme.finiteEtaleTwistPullbackData A N hN hA
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
        (Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom ≫
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

private theorem shifted_square
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift D' ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [F'.CommShift ℤ] [G'.CommShift ℤ]
    [H.CommShift ℤ] (c₁ : H ≅ F ⋙ G) (c₂ : H ≅ F' ⋙ G')
    [NatTrans.CommShift c₁.hom ℤ] [NatTrans.CommShift c₂.hom ℤ]
    {K : C} {L : D} {L' : D'} {M : E}
    (a : F.obj K ⟶ L) (b : G.obj L ⟶ M)
    (a' : F'.obj K ⟶ L') (b' : G'.obj L' ⟶ M) (d : H.obj K ⟶ M)
    (h₁ : c₁.hom.app K ≫ G.map a ≫ b = d)
    (h₂ : c₂.hom.app K ≫ G'.map a' ≫ b' = d) (n : ℤ) :
    (c₁.symm ≪≫ c₂).hom.app (K⟦n⟧) ≫
        G'.map (shiftedHom F' a' n) ≫ shiftedHom G' b' n =
      G.map (shiftedHom F a n) ≫ shiftedHom G b n := by
  have h₁' := shift_composite F G H c₁ a b d h₁ n
  have h₂' := shift_composite F' G' H c₂ a' b' d h₂ n
  have hh := congrArg (fun k ↦ c₁.inv.app (K⟦n⟧) ≫ k) (h₂'.trans h₁'.symm)
  simpa only [shiftedHom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc] using hh

private theorem exactLine_square (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) :
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≫
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
        (exactLine A q (t.line q hY)) ≫
      exactLine A g (t.line g hX) =
      (upperStar (ModuleCat.{u + 1} A) q').mapDerivedCategory.map
        (exactLine A f (t.line f hY)) ≫
      exactLine A q' (t.line q' hY') := by
  let c₁ := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) q' f (g ≫ q) sq.w) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  let c₂ := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) g q) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have hs : exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq = c₁.symm ≪≫ c₂ := by
    apply Iso.ext
    simp [exactDerivedSquareUpperStarIso, squareUpperStarIso, c₁, c₂,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc]
  have : NatTrans.CommShift c₁.hom ℤ := by
    dsimp only [c₁, Iso.trans_hom]
    infer_instance
  have : NatTrans.CommShift c₂.hom ℤ := by
    dsimp only [c₂, Iso.trans_hom]
    infer_instance
  have hc₁ := exactLine₀_comp A q' f (g ≫ q) sq.w
    (t.line f hY) (t.line q' hY') (t.line (g ≫ q) hY)
    (line_comp A N hN hA t q' f hY hY' (g ≫ q) sq.w).symm
  have hc₂ := exactLine₀_comp A g q (g ≫ q) rfl
    (t.line q hY) (t.line g hX) (t.line (g ≫ q) hY)
    (line_comp A N hN hA t g q hY hX).symm
  rw [hs]
  unfold exactLine
  exact shifted_square _ _ _ _ _ c₁ c₂
    (exactLine₀ A f (t.line f hY)) (exactLine₀ A q' (t.line q' hY'))
    (exactLine₀ A q (t.line q hY)) (exactLine₀ A g (t.line g hX))
    (exactLine₀ A (g ≫ q) (t.line (g ≫ q) hY)) hc₁ hc₂ (2 : ℤ)

private theorem mate_twisted_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}
    (s : G ⋙ L₂ ⟶ L₁ ⋙ H)
    {K : C} {P : D} {K' : E} {P' : F}
    (a : L₁.obj K ⟶ P) (b : G.obj K ⟶ K') (c : H.obj P ⟶ P')
    (d : L₂.obj K' ⟶ P')
    (hc : s.app K ≫ H.map a ≫ c = L₂.map b ≫ d) :
    G.map (a₁.unit.app K ≫ R₁.map a) ≫
        (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ s)).app P ≫ R₂.map c =
      b ≫ a₂.unit.app K' ≫ R₂.map d := by
  simp only [Functor.map_comp, Category.assoc]
  erw [((mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ s)).naturality_assoc a)]
  erw [reassoc_of% unit_mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ s) K]
  change a₂.unit.app (G.obj K) ≫ R₂.map (s.app K) ≫ R₂.map (H.map a) ≫ R₂.map c = _
  simp only [← Functor.map_comp, hc]
  rw [Functor.map_comp]
  exact a₂.unit_naturality_assoc b (R₂.map d)

private theorem compared_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {R₁ : D ⥤ C} {R₂ : F ⥤ E} {G₀ G : C ⥤ E} {H₀ H : D ⥤ F}
    (e : G₀ ≅ G) (e' : H₀ ≅ H) (m : R₁ ⋙ G ⟶ H ⋙ R₂)
    {K : C} {P : D} {K' : E} {P' : F}
    (u : K ⟶ R₁.obj P) (u' : K' ⟶ R₂.obj P')
    (b : G.obj K ⟶ K') (c : H.obj P ⟶ P')
    (b₀ : G₀.obj K ⟶ K') (c₀ : H₀.obj P ⟶ P')
    (v : K ⟶ R₁.obj P) (v' : K' ⟶ R₂.obj P')
    (hu : v = u) (hu' : v' = u')
    (hb : b₀ = e.hom.app K ≫ b) (hc : c₀ = e'.hom.app P ≫ c)
    (hm : G.map u ≫ m.app P ≫ R₂.map c = b ≫ u') :
    G₀.map v ≫ (e.hom.app (R₁.obj P) ≫ m.app P ≫ R₂.map (e'.inv.app P)) ≫
        R₂.map c₀ = b₀ ≫ v' := by
  rw [hu, hu', hb, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R₂.map_comp_assoc, Iso.inv_hom_id_app, R₂.map_id, Category.id_comp]
  rw [e.hom.naturality_assoc, hm]

private theorem p1Unit_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    ordinaryFiniteP1Unit A N hA t S hS =
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (ProjectiveLine S ↘ S)).unit.app _ ≫
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
        (exactLine A (ProjectiveLine S ↘ S) (t.line (ProjectiveLine S ↘ S) hS)) := by
  rw [ordinaryFiniteP1Unit, shiftedLine_eq, mapDerivedUpperStarLowerStarAdjunction_eq]
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rfl

/-- The twisted unit commutes with projective-line exchange over arbitrary bases.
Source: blueprint lemma-cohomology-projective-line-trace, base-change paragraph, and
lem-sp-finite-p1-kummer-naturality, step 3.
(auxiliary; not a blueprint node).

Proof: the roots comparison is unique since the kernel inclusion into G_m is
monic. The pure-tensor generators then determine the coefficient-line comparison.
Identify the normalized transport with the finite-twist transport, which satisfies
composition. Applying the degree-zero and shift comparisons gives the commuting
square of shifted-line comparisons around the projective-line square. The exact
inverse-image square descends to derived categories, and its mate is the specified
exchange. The mate-unit identity identifies the image of the q-unit followed by
exchange with the q'-unit followed by the inverse-image square. Postcompose with
the shifted-line transport and substitute its commuting square. Naturality of the
q'-unit gives exactly the displayed equation. This uses neither invertibility of
exchange nor a splitting. Normalization and the mate identity also apply to the
empty scheme, the zero coefficient ring, and N=1. -/
theorem ordinaryFiniteP1_twisted_unit_baseChange
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤))) :
    (ordinaryFinitePullback A f).map (ordinaryFiniteP1Unit A N hA t S hS) ≫
        ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
      (ordinaryFiniteShiftedLinePullback A N hA t f hS).hom ≫
        ordinaryFiniteP1Unit A N hA t S' hS' := by
  let q := ProjectiveLine S ↘ S
  let q' := ProjectiveLine S' ↘ S'
  let g := ProjectiveSpace.map (ULift.{u} (Fin 2)) f
  let hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)) :=
    (map_natCast q.appTop.hom N) ▸ hS.map q.appTop.hom
  have hs := exactLine_square A N hN hA t
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq hS hS' hP
  have hm := mate_twisted_unit
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q')
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq).hom
    (exactLine A q (t.line q hS))
    (exactLine A f (t.line f hS))
    (exactLine A g (t.line g hP))
    (exactLine A q' (t.line q' hS')) hs
  exact compared_square
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq)
    _ _ (exactLine A f (t.line f hS)) (exactLine A g (t.line g hP)) _ _ _ _
    (p1Unit_eq A N hA t S hS) (p1Unit_eq A N hA t S' hS')
    (shiftedLine_eq A N hA t f hS) (shiftedLine_eq A N hA t g hP) hm

end AlgebraicGeometry.Etale
