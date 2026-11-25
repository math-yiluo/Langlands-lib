/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Coherence of the shifted finite Tate line

Source: blueprint lemma-cohomology-projective-line-trace, base-change paragraph. The
positive-case degree-zero and shift calculations reuse proved private helpers
from FiniteP1TwistedUnitBaseChange; the final square also covers N = 0.
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
    (DerivedCategory.singleFunctor E 0) F G H
    F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory e
    (Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm)
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
  exact shifted_square
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) q').mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) q).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (g ≫ q)).mapDerivedCategory c₁ c₂
    (exactLine₀ A f (t.line f hY)) (exactLine₀ A q' (t.line q' hY'))
    (exactLine₀ A q (t.line q hY)) (exactLine₀ A g (t.line g hX))
    (exactLine₀ A (g ≫ q) (t.line (g ≫ q) hY)) hc₁ hc₂ (2 : ℤ)

private theorem compare_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (G G₀ : C ⥤ E) (L L₀ : C ⥤ D) (H H₀ : D ⥤ F) (J J₀ : E ⥤ F)
    (iG : G ≅ G₀) (iL : L ≅ L₀) (iH : H ≅ H₀) (iJ : J ≅ J₀)
    (s : G ⋙ J ⟶ L ⋙ H) (s₀ : G₀ ⋙ J₀ ⟶ L₀ ⋙ H₀)
    {K : C} {P : D} {K' : E} {P' : F}
    (a : L₀.obj K ⟶ P) (b : G₀.obj K ⟶ K')
    (c : H₀.obj P ⟶ P') (d : J₀.obj K' ⟶ P')
    (hs : s.app K = iJ.hom.app (G.obj K) ≫ J₀.map (iG.hom.app K) ≫
      s₀.app K ≫ H₀.map (iL.inv.app K) ≫ iH.inv.app (L.obj K))
    (hc : s₀.app K ≫ H₀.map a ≫ c = J₀.map b ≫ d) :
    s.app K ≫ H.map (iL.hom.app K ≫ a) ≫ (iH.hom.app P ≫ c) =
      J.map (iG.hom.app K ≫ b) ≫ (iJ.hom.app K' ≫ d) := by
  rw [hs]
  simp only [Category.assoc]
  rw [iH.hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
  rw [← H₀.map_comp_assoc, Iso.inv_hom_id_app, H₀.map_id, Category.id_comp]
  rw [hc]
  rw [← iJ.hom.naturality_assoc, ← iJ.hom.naturality_assoc]

private theorem derived_square_comparison
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    (K : DerivedCategoryModule A Y) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) q').hom.app
        ((ordinaryFinitePullback A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) q').mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K ≫
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) q).inv.app K) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app
        ((ordinaryFinitePullback A q).obj K) := by
  simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
    exactDerivedSquareUpperStarIso, squareUpperStarIso,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.inv_hom_id_app_assoc]
  rfl

private theorem shifted_line_square_pos
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A g).map (ordinaryFiniteShiftedLinePullback A N hA t q hY).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t g hX).hom =
    (ordinaryFinitePullback A q').map (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t q' hY').hom := by
  simp only [shiftedLine_eq]
  exact compare_square
    (ordinaryFinitePullback A f) (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (ordinaryFinitePullback A q) (upperStar (ModuleCat.{u + 1} A) q).mapDerivedCategory
    (ordinaryFinitePullback A g) (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (ordinaryFinitePullback A q') (upperStar (ModuleCat.{u + 1} A) q').mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) q)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) q')
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom
    (exactLine A q (t.line q hY)) (exactLine A f (t.line f hY))
    (exactLine A g (t.line g hX)) (exactLine A q' (t.line q' hY'))
    (derived_square_comparison A sq _)
    (exactLine_square A N hN hA t sq hY hY' hX)

/-- The normalized shifted finite Tate line respects every commuting square.
Source: Stacks, Tags 03PK and 03Q1, and the normalized comparisons in blueprint
thm-amb-p1-decomposition.proof.md, base-change paragraph.
(auxiliary; not a blueprint node)

Proof: the roots inclusion determines its comparison uniquely, and pure scalar
root generators determine the coefficient-line comparison. Identify the given
transport with the canonical finite-twist transport, whose comparisons compose.
Apply the single-degree functors and the canonical shift comparisons to the two
compositions around the square. Their common composite identifies the two paths.
The canonical exact/left-derived inverse-image comparison transports this equality
with its naturality constraints. If N is zero, invertibility on Y forces Y, hence
Xprime, to be empty: a point would give a nontrivial stalk and a homomorphism from
its global functions. All derived objects on Xprime are then zero, so its two
arrows agree. No trace, projective-line splitting or properness enters. -/
theorem ordinaryFiniteShiftedLinePullback_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A g).map (ordinaryFiniteShiftedLinePullback A N hA t q hY).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t g hX).hom =
    (ordinaryFinitePullback A q').map (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t q' hY').hom := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : IsEmpty X' := ⟨fun x ↦ by
      let y := q (g x)
      have : Nontrivial Γ(Y, ⊤) := (Y.presheaf.germ ⊤ y trivial).hom.domain_nontrivial
      exact (not_isUnit_zero : ¬ IsUnit (0 : Γ(Y, ⊤))) (by simpa only [Nat.cast_zero] using hY)⟩
    exact (DerivedCategory.isZero_of_forall_isZero
      (Scheme.Etale.isZero_sheaf_of_isEmpty ·)
      ((ordinaryFiniteLine A 0 hA X')⟦(2 : ℤ)⟧)).eq_of_tgt _ _
  · exact shifted_line_square_pos A N hN hA t sq hY hY' hX

end AlgebraicGeometry.Etale
