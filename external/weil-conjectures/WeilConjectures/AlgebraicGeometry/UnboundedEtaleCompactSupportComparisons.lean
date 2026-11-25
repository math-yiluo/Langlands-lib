/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
public import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenComposition
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenInterchange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat

/-!
# Unbounded ordinary etale compact-support comparisons

Source: Stacks Project, Tags 0F7H--0F7L and 0F7B, case (b)
(auxiliary; not a blueprint node).

The candidates, common-refinement comparisons, and proper/open tower isomorphism are the
existing ordinary etale constructions. The definitions below assemble the specified tower
composition and transport the existing exchange to exact, termwise inverse image. The
statements supply coherence and equality with the bounded-below maps, on actual natural
transformations rather than just existence of unrelated isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α) =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private lemma mate_whiskerTop
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

set_option backward.isDefEq.respectTransparency false in
private lemma exact_exchange_transport
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g').hom _ =
      exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq := by
  let B := ModuleCat.{u + 1} A
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq).hom
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory B g').inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory B f').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B f).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso B sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar B g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  have hm := mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction B f) (derivedUpperStarLowerStarAdjunction B f')
    (leftDerivedUpperStarIsoMapDerivedCategory B f)
    (leftDerivedUpperStarIsoMapDerivedCategory B f')
    ((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory B g').inv)
  rw [← mapDerivedUpperStarLowerStarAdjunction_eq,
    ← mapDerivedUpperStarLowerStarAdjunction_eq, hs] at hm
  change _ = derivedBaseChangeMap B sq at hm
  rw [← hm]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [mate_whiskerBottom, mate_whiskerTop]
  change _ = (mateEquiv (mapDerivedUpperStarLowerStarAdjunction B f)
    (mapDerivedUpperStarLowerStarAdjunction B f') α).app K
  dsimp only [B, rightDerivedLowerStar, Functor.comp_obj]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Assemble the canonical proper/open tower comparison, using the closure compactification
`ofComp`, and compare the input and output with the chosen compactifications. This is the
explicit isomorphism in the proof of the existing unbounded composition theorem.
Source: Stacks Project, Tag 0F7J
(auxiliary; not a blueprint node). -/
noncomputable def unboundedEtaleLowerShriekCompIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekIso A
        ((HasCompactification.compactification (f ≫ g)).ofComp
          (HasCompactification.compactification g)).restrict).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A
      (HasCompactification.compactification g)
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)) ≪≫
    rightDerivedLowerShriekIso A
      ((HasCompactification.compactification g).comp
        ((HasCompactification.compactification (f ≫ g)).ofComp
          (HasCompactification.compactification g)))

/-- Transport the already defined unbounded exchange from left derived inverse image to
its exact termwise realization. No new choice of exchange map is made.
Source: Stacks Project, Tag 0F7L
(auxiliary; not a blueprint node). -/
noncomputable def unboundedEtaleCompactSupportBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' :=
  Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).inv ≫
    rightDerivedLowerShriekBaseChangeMap A sq ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v').hom _

section UnboundedFormalism

private lemma derived_iso_trans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_trans e d)

private lemma derived_iso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_symm e)

private lemma derived_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    (FG : C₀ ⥤ C₂) (GH : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH ≪≫ Functor.isoWhiskerLeft F eGH =
      eFG_H ≪≫ Functor.isoWhiskerRight eFG H) :
    (Functor.mapDerivedCategoryTriangleIso eF_GH).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso eGH).hom =
      (Functor.mapDerivedCategoryTriangleIso eFG_H).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eFG).hom
          H.mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F GH).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft,
    Category.assoc, ← Category.assoc (Functor.mapDerivedCategoryCompIso FG H).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  simp only [← Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_trans, h,
    Functor.mapDerivedCategoryNatIso_trans]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_assoc]

private lemma derived_unit_right
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (I : D ⥤ D) [F.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : I ≅ 𝟭 D) (m : F ≅ F ⋙ I)
    (h : m ≪≫ Functor.isoWhiskerLeft F e = (Functor.rightUnitor F).symm) :
    (Functor.mapDerivedCategoryTriangleIso m).hom ≫
      Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom =
      𝟙 _ := by
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F I).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft]
  simp only [← Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_trans, h]
  simp only [Category.assoc]
  change (Functor.mapDerivedCategoryNatIso (Iso.refl F)).hom ≫ _ = _
  rw [Functor.mapDerivedCategoryNatIso_refl]
  simp only [Category.id_comp]
  exact Functor.mapDerivedCategoryCompIso_comp_id F

private lemma derived_unit_left
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (I : C ⥤ C) [F.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : I ≅ 𝟭 C) (m : F ≅ I ⋙ F)
    (h : m ≪≫ Functor.isoWhiskerRight e F = (Functor.leftUnitor F).symm) :
    (Functor.mapDerivedCategoryTriangleIso m).hom ≫
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom
        F.mapDerivedCategory = 𝟙 _ := by
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso I F).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  simp only [← Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_trans, h]
  simp only [Category.assoc]
  change (Functor.mapDerivedCategoryNatIso (Iso.refl F)).hom ≫ _ = _
  rw [Functor.mapDerivedCategoryNatIso_refl]
  simp only [Category.id_comp]
  exact Functor.mapDerivedCategoryCompIso_id_comp F

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso

private noncomputable def exact_pb_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z := f ≫ g)
    (hfg : fg = f ≫ g := by cat_disch) :
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg)

private lemma exact_pb_comp_assoc
    (A : Type (u + 1)) [CommRing A] {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    (exact_pb_comp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (exact_pb_comp A g h gh hgh).hom
          (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory =
      (exact_pb_comp A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
          (exact_pb_comp A f g fg hfg).hom := by
  let B := ModuleCat.{u + 1} A
  have he : upperStarComp B fg h fgh hfgh ≪≫
        Functor.isoWhiskerLeft (upperStar B h) (upperStarComp B f g fg hfg) =
      upperStarComp B f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc]) ≪≫
        Functor.isoWhiskerRight (upperStarComp B g h gh hgh) (upperStar B f) := by
    apply Iso.ext
    exact (upperStarComp_assoc' B f g h fg gh fgh hfg hgh hfgh).symm
  exact (derived_triangle_assoc (upperStar B h) (upperStar B g) (upperStar B f)
    (upperStar B gh) (upperStar B fg) (upperStar B fgh)
    (upperStarComp B g h gh hgh) (upperStarComp B f g fg hfg)
    (upperStarComp B fg h fgh hfgh)
    (upperStarComp B f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])) he).symm

private lemma exact_pb_comp_congr
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (d d' : X ⟶ Z)
    (hd : d = f ≫ g) (hd' : d' = f ≫ g)
    (M : DerivedCategoryModule A Z) :
    (exact_pb_comp A f g d hd).hom.app M =
      eqToHom (by rw [hd, hd']) ≫ (exact_pb_comp A f g d' hd').hom.app M := by
  subst hd hd'
  simp

private noncomputable def exact_pb_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory ≅
      𝟭 (DerivedCategoryModule A X) :=
  Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

private lemma exact_pb_id_left
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exact_pb_comp A (𝟙 X) f f (Category.id_comp f).symm).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
        (exact_pb_id A X).hom = 𝟙 _ := by
  apply derived_unit_right
  rw [upperStarComp_id_left]
  apply Iso.ext
  ext M
  simp

private lemma exact_pb_id_right
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exact_pb_comp A f (𝟙 Y) f (Category.comp_id f).symm).hom ≫
      Functor.whiskerRight (exact_pb_id A Y).hom
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory = 𝟙 _ := by
  apply derived_unit_left
  rw [upperStarComp_id_right]
  apply Iso.ext
  ext M
  simp

private noncomputable def unboundedFormalism
    (A : Type (u + 1)) [CommRing A] : CompactSupportFormalism where
  obj X := DerivedCategoryModule A X
  category X := inferInstanceAs (Category.{u + 1} (DerivedCategoryModule A X))
  pb f := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  pbId X := exact_pb_id A X
  pbComp f g := exact_pb_comp A f g
  pbComp_assoc f g h M := by
    have hh := NatTrans.congr_app
      (exact_pb_comp_assoc A f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hh
    rw [← hh, exact_pb_comp_congr A f (g ≫ h) _ (f ≫ g ≫ h)
      (Category.assoc _ _ _) rfl]
    simp only [Category.assoc, Functor.comp_obj]
  pbId_comp f M := by
    have hh := NatTrans.congr_app (exact_pb_id_left A f) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hh
    rw [exact_pb_comp_congr A (𝟙 _) f _ f rfl (Category.id_comp f).symm]
    rw [Category.assoc, hh]
    simp only [Category.comp_id]
  pbComp_id f M := by
    have hh := NatTrans.congr_app (exact_pb_id_right A f) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hh
    rw [exact_pb_comp_congr A f (𝟙 _) _ f rfl (Category.comp_id f).symm]
    rw [Category.assoc, hh]
    simp only [Category.comp_id]
  pf f := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  adj f := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  sh j hj := haveI := hj.out; (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  shAdj j hj := haveI := hj.out; (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction

private lemma derived_square_symm
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {P : C ⥤ D} {Q : D ⥤ F} {R : C ⥤ E} {S : E ⥤ F}
    [P.Additive] [Q.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : P ⋙ Q ≅ R ⋙ S) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]

private lemma open_exchange_mate_coefficients
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).hom =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction B r
          ).mapDerivedCategoryAdjunction
        (openImmersionLowerShriekUpperStarAdjunction B l
          ).mapDerivedCategoryAdjunction).symm
        (TwoSquare.mk _ _ _ _
          (exactDerivedSquareUpperStarIso B sq.toCommSq).inv)) := by
  let := isIso_openImmersionLowerShriekBaseChangeMap B sq
  have h := mateEquiv_eq_of_unit
    (openImmersionLowerShriekUpperStarAdjunction B r).mapDerivedCategoryAdjunction
    (openImmersionLowerShriekUpperStarAdjunction B l).mapDerivedCategoryAdjunction
    (TwoSquare.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).hom)
    (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq.toCommSq).inv) (fun K ↦ ?_)
  · exact (((mateEquiv _ _).symm_apply_eq.mpr h.symm)).symm
  have hK := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction B r)
    (openImmersionLowerShriekUpperStarAdjunction B l)
    (squareUpperStarIso B sq.toCommSq.flip)
    (asIso (openImmersionLowerShriekBaseChangeMap B sq.toCommSq))
    (unit_map_openImmersionLowerShriekBaseChangeMap_app B sq.toCommSq) K
  rewrite [squareUpperStarIso_flip, derived_square_symm] at hK
  exact hK.symm

private lemma unbounded_pb_comp'
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (w : f ≫ g = fg) :
    (unboundedFormalism A).pbComp' f g fg w = exact_pb_comp A f g fg w.symm := by
  subst w
  rw [ExchangeFormalism.pbComp'_rfl]
  rfl

private lemma unbounded_sq_iso
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} (sq : CommSq t l r b) :
    (unboundedFormalism A).sqIso t l r b sq.w =
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  apply Iso.ext
  simp only [ExchangeFormalism.sqIso, unbounded_pb_comp', exact_pb_comp,
    Functor.mapDerivedCategoryTriangleIso, exactDerivedSquareUpperStarIso,
    squareUpperStarIso, derived_iso_trans,
    derived_iso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]

private lemma unbounded_open_base_change
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    ((unboundedFormalism A).baseChange t l r b sq.w) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).hom := by
  rw [ExchangeFormalism.baseChange, unbounded_sq_iso]
  exact (open_exchange_mate_coefficients (ModuleCat.{u + 1} A) sq).symm

private local instance unbounded_has_base_change
    (A : Type (u + 1)) [CommRing A] : (unboundedFormalism A).HasBaseChange where
  isIso_baseChange sq := by
    rw [unbounded_open_base_change A sq]
    infer_instance

private lemma unbounded_open_exchange
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := unboundedFormalism A) sq
    ((unboundedFormalism A).exchange t l r b sq.w) =
      openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) sq
  dsimp only [ExchangeFormalism.exchange, openImmersionLowerShriekLowerStarExchange]
  have hh : inv ((unboundedFormalism A).baseChange t l r b sq.w) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change A sq]
    exact Iso.hom_inv_id _
  rw [hh]
  rfl

private local instance unbounded_has_proper_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    (unboundedFormalism A).HasProperExchange where
  isIso_exchange sq := by
    rw [unbounded_open_exchange A sq]
    exact isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring A
      isAddTorsion_of_finite sq

private lemma unbounded_pf_comp_inv
    (A : Type (u + 1)) [CommRing A] {T S R : Scheme.{u}}
    (f : T ⟶ S) (g : S ⟶ R) (fg : T ⟶ R) (w : f ≫ g = fg) :
    ((unboundedFormalism A).pfComp' f g fg w).inv =
      (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
        (lowerStar (ModuleCat.{u + 1} A) g)
        (lowerStarComp (ModuleCat.{u + 1} A) f g fg w.symm)).hom := by
  let B := ModuleCat.{u + 1} A
  have hh := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction B f) (upperStarLowerStarAdjunction B g)
    (upperStarLowerStarAdjunction B fg) (lowerStarComp B f g fg w.symm)
    (upperStarComp B f g fg w.symm) (by
      exact (congrArg Iso.hom
        (conjugateIsoEquiv_upperStarComp B f g fg w.symm)).symm)
  rw [ExchangeFormalism.pfComp', unbounded_pb_comp']
  exact hh.symm

section ExactOpenComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe vC vD vE uC uD uE wC wD wE

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma exact_unit_ext
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {F G : DerivedCategory C ⥤ DerivedCategory C} {α β : F ⟶ G}
    (h : ∀ K : HomotopyCategory C (.up ℤ),
      α.app (DerivedCategory.Qh.obj K) = β.app (DerivedCategory.Qh.obj K)) : α = β := by
  exact Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) h

private lemma exact_adj_comp
    {C : Type uC} {D : Type uD} {E : Type uE} [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    [Abelian C] [Abelian D] [Abelian E]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D] [IsGrothendieckAbelian.{vE} E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) :
    (a.comp b).mapDerivedCategoryAdjunction =
      ((a.mapDerivedCategoryAdjunction.comp b.mapDerivedCategoryAdjunction
        ).ofNatIsoLeft (Functor.mapDerivedCategoryCompIso L₁ L₂)
          ).ofNatIsoRight (Functor.mapDerivedCategoryCompIso R₂ R₁) := by
  apply Adjunction.ext
  apply exact_unit_ext (C := C)
  intro K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_unit_app]
  let KL := ((L₁ ⋙ L₂).mapHomotopyCategory (.up ℤ)).obj K
  rw [← cancel_mono ((R₂ ⋙ R₁).mapDerivedCategory.map
    ((L₁ ⋙ L₂).mapDerivedCategoryFactorsh.hom.app K) ≫
      (R₂ ⋙ R₁).mapDerivedCategoryFactorsh.hom.app KL)]
  simp only [Category.assoc]
  rw [(a.comp b).mapDerivedCategoryAdjunction_unit_app_fac K]
  have hL : (Functor.mapDerivedCategoryCompIso L₁ L₂).hom.app
      (DerivedCategory.Qh.obj K) ≫ (L₁ ⋙ L₂).mapDerivedCategoryFactorsh.hom.app K =
      L₂.mapDerivedCategory.map (L₁.mapDerivedCategoryFactorsh.hom.app K) ≫
        L₂.mapDerivedCategoryFactorsh.hom.app ((L₁.mapHomotopyCategory (.up ℤ)).obj K) := by
    rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso L₁ L₂).inv.app
      (DerivedCategory.Qh.obj K)), Iso.inv_hom_id_app_assoc]
    exact (Functor.mapDerivedCategoryCompIso_hom_app_factorsh L₁ L₂ K).symm
  have hR : (Functor.mapDerivedCategoryCompIso R₂ R₁).hom.app
      (DerivedCategory.Qh.obj KL) ≫ (R₂ ⋙ R₁).mapDerivedCategoryFactorsh.hom.app KL =
      R₁.mapDerivedCategory.map (R₂.mapDerivedCategoryFactorsh.hom.app KL) ≫
        R₁.mapDerivedCategoryFactorsh.hom.app ((R₂.mapHomotopyCategory (.up ℤ)).obj KL) := by
    rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso R₂ R₁).inv.app
      (DerivedCategory.Qh.obj KL)), Iso.inv_hom_id_app_assoc]
    exact (Functor.mapDerivedCategoryCompIso_hom_app_factorsh R₂ R₁ KL).symm
  have hn := (Functor.mapDerivedCategoryCompIso R₂ R₁).hom.naturality
    ((L₁ ⋙ L₂).mapDerivedCategoryFactorsh.hom.app K)
  simp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  rw [hR]
  simp only [Functor.comp_map]
  slice_rhs 3 4 =>
    erw [← R₁.mapDerivedCategory.map_comp, ← R₂.mapDerivedCategory.map_comp, hL]
  simp only [Functor.map_comp, Category.assoc]
  have hη := b.mapDerivedCategoryAdjunction.unit.naturality
    (L₁.mapDerivedCategoryFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.id_map] at hη
  slice_rhs 2 3 =>
    erw [← R₁.mapDerivedCategory.map_comp, ← hη]
  simp only [Functor.map_comp, Category.assoc]
  slice_rhs 3 5 =>
    erw [← R₁.mapDerivedCategory.map_comp_assoc,
      ← R₁.mapDerivedCategory.map_comp, Category.assoc,
      b.mapDerivedCategoryAdjunction_unit_app_fac]
  have hN := R₁.mapDerivedCategoryFactorsh.hom.naturality
    ((b.mapHomotopyCategory (.up ℤ)).unit.app ((L₁.mapHomotopyCategory (.up ℤ)).obj K))
  simp only [Functor.comp_map] at hN
  erw [hN]
  erw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_fac K)]
  rw [← Functor.map_comp]
  congr 1
  rw [Adjunction.mapHomotopyCategory_comp_unit_app]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.comp_id]
private lemma exact_adj_conjugate
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (r : R₂ ≅ R₁)
    (h : ∀ K, a.unit.app K ≫ R₁.map (e.hom.app K) =
      b.unit.app K ≫ r.hom.app (L₂.obj K)) :
    a.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom R₁.mapDerivedCategory =
      b.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerLeft L₂.mapDerivedCategory (Functor.mapDerivedCategoryNatIso r).hom := by
  apply exact_unit_ext (C := C)
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (R₁.mapDerivedCategory.map (L₂.mapDerivedCategoryFactorsh.hom.app K) ≫
    R₁.mapDerivedCategoryFactorsh.hom.app ((L₂.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  have he := Functor.mapDerivedCategoryNatIso_fach e K
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, he, Functor.map_comp]
  have hNR := R₁.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K)
  simp only [Functor.comp_map] at hNR
  simp only [Category.assoc]
  erw [hNR]
  erw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_fac K)]
  have hN := (Functor.mapDerivedCategoryNatIso r).hom.naturality
    (L₂.mapDerivedCategoryFactorsh.hom.app K)
  erw [← reassoc_of% hN]
  erw [Functor.mapDerivedCategoryNatIso_fach r]
  erw [reassoc_of% (b.mapDerivedCategoryAdjunction_unit_app_fac K)]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ) a b e.hom r.hom h K
private lemma derived_open_comp_conjugate
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) [IsOpenImmersion j₁] [IsOpenImmersion j₂] :
    conjugateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction B j₁
        ).mapDerivedCategoryAdjunction.comp
        (openImmersionLowerShriekUpperStarAdjunction B j₂
          ).mapDerivedCategoryAdjunction)
      (openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
        ).mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategoryTriangleIso
        (openImmersionLowerShriekComp B j₁ j₂)).hom =
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp B j₁ j₂)).inv := by
  let a := openImmersionLowerShriekUpperStarAdjunction B j₁
  let b := openImmersionLowerShriekUpperStarAdjunction B j₂
  let c := openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
  let e := openImmersionLowerShriekComp B j₁ j₂
  let r := upperStarComp B j₁ j₂
  have hu (K : Sheaf X.smallEtaleTopology B) :
      c.unit.app K ≫ (upperStar B (j₁ ≫ j₂)).map (e.hom.app K) =
        (a.comp b).unit.app K ≫ r.inv.app
          (((openImmersionLowerShriek B j₁) ⋙ (openImmersionLowerShriek B j₂)).obj K) := by
    exact Adjunction.unit_leftAdjointUniq_hom_app c ((a.comp b).ofNatIsoRight r.symm) K
  have hd := exact_adj_conjugate
    (C := Sheaf X.smallEtaleTopology B) (D := Sheaf Z.smallEtaleTopology B)
    c (a.comp b) e r.symm hu
  rw [exact_adj_comp (C := Sheaf X.smallEtaleTopology B)
    (D := Sheaf Y.smallEtaleTopology B) (E := Sheaf Z.smallEtaleTopology B) a b] at hd
  apply conjugateEquiv_eq_of_unit
  intro K
  have hK := congrArg (fun t ↦ t.app K) hd
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_unit_app,
    Functor.mapDerivedCategoryNatIso_symm] at hK
  let L₁ := openImmersionLowerShriek B j₁
  let L₂ := openImmersionLowerShriek B j₂
  let R := upperStar B (j₁ ≫ j₂)
  let R₁ := upperStar B j₁
  let R₂ := upperStar B j₂
  have hk := congrArg (fun t ↦ t ≫ R.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).inv.app K)) hK
  simp only [Category.assoc] at hk
  have hn := (Functor.mapDerivedCategoryTriangleIso r).inv.naturality
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).inv.app K)
  simp only [Functor.comp_map] at hn
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc] at hn
  erw [← hn] at hk
  erw [← (R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory).map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hk
  simpa only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Adjunction.comp_unit_app,
    a, b, c, e, r, L₁, L₂, R, R₁, R₂, Category.assoc] using hk.symm

end ExactOpenComposition

section IdentityComparisons
universe vC vD uC uD wC wD v w
attribute [local irreducible] Adjunction.mapDerivedCategoryAdjunction
private lemma exact_adj_id
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    (Adjunction.id (C := C)).mapDerivedCategoryAdjunction =
      ((Adjunction.id (C := DerivedCategory C)).ofNatIsoLeft
        (Functor.mapDerivedCategoryIdIso C).symm).ofNatIsoRight
        (Functor.mapDerivedCategoryIdIso C).symm := by
  apply Adjunction.ext
  apply exact_unit_ext (C := C)
  intro K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom]
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Category.id_comp]
  rw [← cancel_mono ((𝟭 C).mapDerivedCategory.map
    ((𝟭 C).mapDerivedCategoryFactorsh.hom.app K) ≫
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app
        (((𝟭 C).mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  erw [(Adjunction.id (C := C)).mapDerivedCategoryAdjunction_unit_app_fac K]
  have hn := (Functor.mapDerivedCategoryIdIso C).inv.naturality
    ((𝟭 C).mapDerivedCategoryFactorsh.hom.app K)
  dsimp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  rw [← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Iso.inv_hom_id_app]
  rw [Adjunction.mapHomotopyCategory_id_unit_app]
  have hi (K' : HomotopyCategory C (.up ℤ)) :
      (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).inv.app K' = 𝟙 K' := by
    apply (cancel_mono ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app K')).mp
    erw [Iso.inv_hom_id_app, Functor.mapHomotopyCategoryIdIso_hom_app_eq_id,
      Category.id_comp]
    rfl
  erw [hi]
  repeat erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact DerivedCategory.Qh.map_id K
private lemma identity_conjugate_of_unit
    {C : Type*} [Category C] {L R I : C ⥤ C}
    (a : L ⊣ R) (δ : I ≅ 𝟭 C) (e : L ≅ I) (r : R ≅ I)
    (h : a.unit ≫ Functor.whiskerRight e.hom R =
      (((Adjunction.id (C := C)).ofNatIsoLeft δ.symm).ofNatIsoRight δ.symm).unit ≫
        Functor.whiskerLeft I r.inv) :
    conjugateEquiv Adjunction.id a (e ≪≫ δ).hom = (r ≪≫ δ).inv := by
  apply conjugateEquiv_eq_of_unit
  intro K
  have hK := NatTrans.congr_app h K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Adjunction.id_unit,
    Functor.id_map, Category.id_comp] at hK
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.map_comp]
  rw [← Category.assoc, hK]
  simp only [Category.assoc]
  rw [← (r.inv.naturality (δ.hom.app K))]
  rw [← reassoc_of% (δ.inv.naturality (δ.hom.app K))]
  simp only [ ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

private lemma derived_open_id_conjugate
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
        ).mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom =
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).inv := by
  let B := ModuleCat.{u + 1} A
  let a := openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let e := Adjunction.leftAdjointIdIso a (upperStarId B X)
  have hu (K : Sheaf X.smallEtaleTopology B) :
      a.unit.app K ≫ (upperStar B (𝟙 X)).map (e.hom.app K) =
        Adjunction.id.unit.app K ≫ (upperStarId B X).inv.app K := by
    have h := unit_conjugateEquiv Adjunction.id a e.hom K
    simpa only [Adjunction.conjugateEquiv_leftAdjointIdIso_hom, e,
      Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj, Category.id_comp]
      using h.symm
  have hd := exact_adj_conjugate
    (C := Sheaf X.smallEtaleTopology B) (D := Sheaf X.smallEtaleTopology B)
    a Adjunction.id e (upperStarId B X).symm hu
  rw [exact_adj_id (C := Sheaf X.smallEtaleTopology B)] at hd
  apply identity_conjugate_of_unit
  simpa only [Functor.mapDerivedCategoryNatIso_symm] using hd
private lemma exact_right_adj
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    [L₁.Additive] [R₁.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    (a : L₁ ⊣ R₁) :
    a.mapDerivedCategoryAdjunction =
      a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R₁.rightDerivedFunctorIsoMapDerivedCategory := by
  apply Adjunction.ext
  apply exact_unit_ext (C := C)
  intro K
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (R₁.mapDerivedCategory.map
    (L₁.mapDerivedCategoryFactorsh.hom.app K) ≫
      R₁.mapDerivedCategoryFactorsh.hom.app ((L₁.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  rw [a.mapDerivedCategoryAdjunction_unit_app_fac K]
  have hn := R₁.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L₁.mapDerivedCategoryFactorsh.hom.app K)
  rw [← reassoc_of% hn]
  have hη := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L₁.mapDerivedCategoryFactorsh.hom
    R₁.rightDerivedFunctorUnit K
  erw [reassoc_of% hη]
  have hR := NatTrans.congr_app R₁.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L₁.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hR
  rw [← Category.assoc _ _ (R₁.mapDerivedCategoryFactorsh.hom.app _), hR,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

private lemma right_identity_conjugate
    {C : Type*} [Category C] {L R S : C ⥤ C}
    (a : L ⊣ R) (κ : R ≅ S) (e : L ≅ 𝟭 C) (r : S ≅ 𝟭 C)
    (h : conjugateEquiv Adjunction.id (a.ofNatIsoRight κ) e.hom = r.inv) :
    conjugateIsoEquiv a Adjunction.id e.symm = κ ≪≫ r := by
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro K
  have hu := unit_conjugateEquiv Adjunction.id (a.ofNatIsoRight κ) e.hom K
  rw [h] at hu
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.id_unit, NatTrans.id_app,
    Category.id_comp] at hu
  have ht := congrArg (fun t ↦ t ≫ S.map (e.inv.app K) ≫ r.hom.app (L.obj K)) hu
  simp only [Category.assoc] at ht
  rw [← S.map_comp_assoc, Iso.hom_inv_id_app, S.map_id, Category.id_comp] at ht
  rw [r.hom.naturality (e.inv.app K)] at ht
  simp only [Functor.id_obj, Functor.id_map, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp] at ht
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj,
    Category.id_comp, Category.assoc] using ht.symm

private lemma derived_star_id_conjugate
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    conjugateIsoEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
      Adjunction.id
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm =
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
          Functor.mapDerivedCategoryIdIso _ := by
  let B := ModuleCat.{u + 1} A
  have hu (K : Sheaf X.smallEtaleTopology B) :
      (upperStarLowerStarAdjunction B (𝟙 X)).unit.app K ≫
        (lowerStar B (𝟙 X)).map ((upperStarId B X).hom.app K) =
      Adjunction.id.unit.app K ≫ (lowerStarId B X).inv.app K := by
    simpa only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] using
      upperStarId_hom_app_unit_app B X K
  have hd := exact_adj_conjugate
    (C := Sheaf X.smallEtaleTopology B) (D := Sheaf X.smallEtaleTopology B)
    (upperStarLowerStarAdjunction B (𝟙 X))
    Adjunction.id (upperStarId B X) (lowerStarId B X).symm hu
  rw [exact_adj_id (C := Sheaf X.smallEtaleTopology B)] at hd
  have he := identity_conjugate_of_unit
    (upperStarLowerStarAdjunction B (𝟙 X)).mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso (upperStarId B X))
    (Functor.mapDerivedCategoryNatIso (lowerStarId B X))
    (by simpa only [Functor.mapDerivedCategoryNatIso_symm] using hd)
  rw [exact_right_adj (C := Sheaf X.smallEtaleTopology B)
    (D := Sheaf X.smallEtaleTopology B) (upperStarLowerStarAdjunction B (𝟙 X))] at he
  exact right_identity_conjugate _ _ _ _ he

end IdentityComparisons

private lemma composed_iso_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (S : D ⥤ E) (T : C ⥤ E) (e : R ⋙ S ≅ T)
    {K : D} {L M : C} (a : K ⟶ R.obj L) (b : L ⟶ M) :
    S.map (a ≫ R.map b) ≫ e.hom.app M =
      S.map a ≫ e.hom.app L ≫ T.map b := by
  have hn := e.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [S.map_comp, Category.assoc, hn]

private lemma conjugate_iso_symm_eq
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₂ ≅ L₁) (r : R₁ ≅ R₂)
    (h : conjugateEquiv a b e.hom = r.hom) :
    (conjugateIsoEquiv a b).symm r = e := by
  apply (conjugateIsoEquiv a b).symm_apply_eq.mpr
  exact Iso.ext h.symm

section OpenCompositionComparisons

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma unbounded_sh_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j]
    (w : j₁ ≫ j₂ = j) :
    (unboundedFormalism A).shComp' j₁ j₂ j w =
      mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) w.symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) j₁ j₂ := by
  subst j
  rw [ExchangeFormalism.shComp', unbounded_pb_comp']
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.refl_trans]
  apply conjugate_iso_symm_eq
  exact derived_open_comp_conjugate (ModuleCat.{u + 1} A) j₁ j₂

private lemma unbounded_pf_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (unboundedFormalism A).pfComp' f g (f ≫ g) rfl =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).symm := by
  rw [ExchangeFormalism.pfComp', unbounded_pb_comp']
  rfl

private lemma exact_open_congr_symm
    (A : Type (u + 1)) [CommRing A] {U Z : Scheme.{u}} {j j' : U ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j') :
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h.symm =
      (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).symm := by
  subst j'
  rfl

private lemma unbounded_comp_hom_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (K : DerivedCategoryModule A X) :
    ((unboundedFormalism A).compIso T).hom.app K =
      (lowerStar (ModuleCat.{u + 1} A) T.cg.g).rightDerivedFunctor.map
        ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) T.isPullback).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) T.cf.i).mapDerivedCategory.obj K) ≫
        (lowerStar (ModuleCat.{u + 1} A) T.p).rightDerivedFunctor.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) T.cf.i T.q).inv.app K ≫
          (mapDerivedCategoryOpenImmersionLowerShriekCongr
            (ModuleCat.{u + 1} A) T.i_q).hom.app K)) ≫
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} A) T.p)
        (lowerStar (ModuleCat.{u + 1} A) T.cg.g)
        (lowerStarComp (ModuleCat.{u + 1} A) T.p T.cg.g T.cfg.g T.p_g.symm)).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) T.cfg.i).mapDerivedCategory.obj K) := by
  rw [CompactSupportFormalism.compIso_hom_app,
    unbounded_open_exchange A T.isPullback, unbounded_sh_comp,
    exact_open_congr_symm,
    unbounded_pf_comp_inv A T.p T.cg.g T.cfg.g T.p_g]
  · simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
    rfl

private lemma right_derived_star_comp_eq
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Functor.rightDerivedFunctorCompIso'
      (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)
      (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom := by
  have h := unbounded_pf_comp_inv A f g (f ≫ g) rfl
  rw [unbounded_pf_comp] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma unbounded_comp_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    (unboundedFormalism A).compIso (Compactification.Triangle.ofRestrict d e) =
      rightDerivedLowerShriekOfCompactificationCompIso A d e := by
  let B := ModuleCat.{u + 1} A
  have := isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring A
    isAddTorsion_of_finite e.isPullback_restrict
  apply Iso.ext
  apply NatTrans.ext
  funext K
  change DerivedCategoryModule A X at K
  change (_ : ((rightDerivedLowerShriekOfCompactification B e.restrict ⋙
      rightDerivedLowerShriekOfCompactification B d).obj K ⟶
      (rightDerivedLowerShriekOfCompactification B (d.comp e)).obj K)) = _
  rw [unbounded_comp_hom_app]
  dsimp only [Compactification.Triangle.ofRestrict, Compactification.comp,
    Compactification.copy, Compactification.postcomp]
  erw [right_derived_star_comp_eq]
  simp only [rightDerivedLowerShriekOfCompactificationCompIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  exact (composed_iso_naturality
    (lowerStar B e.g).rightDerivedFunctor (lowerStar B d.g).rightDerivedFunctor
    (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor (rightDerivedLowerStarComp B e.g d.g)
    ((openImmersionLowerShriekLowerStarExchange B e.isPullback_restrict).app
      ((openImmersionLowerShriek B e.restrict.i).mapDerivedCategory.obj K))
    ((mapDerivedCategoryOpenImmersionLowerShriekComp B e.restrict.i
      (pullback.fst e.g d.i)).inv.app K ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr B e.restrict_i_fst).hom.app K)).trans
      (Category.id_comp _).symm

end OpenCompositionComparisons

private lemma unbounded_base_change_refinement
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    ((unboundedFormalism A).baseChange (𝟙 X) c.i d.i r.hom hr.flip.w) =
      Functor.whiskerRight ((unboundedFormalism A).pbId X).hom
          ((unboundedFormalism A).sh c.i) ≫
        (Functor.leftUnitor _).hom ≫
          (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hr).hom := by
  let B := ModuleCat.{u + 1} A
  have key := mateEquiv_eq_of_unit ((unboundedFormalism A).shAdj d.i)
    ((unboundedFormalism A).shAdj c.i)
    (TwoSquare.mk ((unboundedFormalism A).pb (𝟙 X)) _ _ ((unboundedFormalism A).pb r.hom)
      (Functor.whiskerRight ((unboundedFormalism A).pbId X).hom
      ((unboundedFormalism A).sh c.i) ≫ (Functor.leftUnitor _).hom ≫
        (refinementLowerShriekBaseChangeDerivedIso B r hr).hom))
    ((unboundedFormalism A).sqIso (𝟙 X) c.i d.i r.hom hr.flip.w).hom (fun K ↦ ?_)
  · rw [ExchangeFormalism.baseChange, ← key]
    exact (Equiv.symm_apply_apply _ _)
  rw [ExchangeFormalism.sqIso_eq _ _ _ _ _ _ d.i (Category.id_comp _) r.i_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.map_comp]
  rw [ExchangeFormalism.pbComp'_id_left_inv_app, unbounded_pb_comp']
  have h₁ := ((unboundedFormalism A).pbId X).hom.naturality
    (((unboundedFormalism A).shAdj d.i).unit.app K)
  have h₂ := ((unboundedFormalism A).shAdj c.i).unit_naturality
    ((exact_pb_id A X).hom.app K)
  have h₃ := unit_map_refinementLowerShriekBaseChangeDerivedIso B r hr K
  rw [upperStarCompIso_eq] at h₃
  erw [reassoc_of% h₁, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h₂]
  exact congrArg (fun t ↦ _ ≫ t) h₃.symm

private theorem unbounded_refinement_comparison
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (unboundedFormalism A).refinementComparison r hr =
      rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr := by
  rw [CompactSupportFormalism.refinementComparison_eq_of_baseChange
    (unboundedFormalism A) r hr
    (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hr)
    (unbounded_base_change_refinement A r hr), unbounded_pf_comp_inv,
    ← refinementLowerStarComp_eq]
  rfl

private theorem unbounded_shriek_iso
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f) :
    (unboundedFormalism A).shriekIso c d =
      rightDerivedLowerShriekOfCompactificationIso A c d := by
  ext : 1
  simp only [CompactSupportFormalism.shriekIso, rightDerivedLowerShriekOfCompactificationIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, unbounded_refinement_comparison]

private lemma unbounded_chosen_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    (unboundedFormalism A).lowerShriekCompIso f g =
      unboundedEtaleLowerShriekCompIso A f g := by
  rw [CompactSupportFormalism.lowerShriekCompIso]
  rw [← CompactSupportFormalism.shriekIso_symm]
  simp only [Compactification.Triangle.ofHasCompactification, unbounded_comp_iso,
    unbounded_shriek_iso, unboundedEtaleLowerShriekCompIso, rightDerivedLowerShriekIso]
  rfl

end UnboundedFormalism

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

/-- The composition isomorphism is computed by every proper/open tower. Thus it is
independent of compactification choices and commutes with their refinement comparisons.
Source: Stacks Project, Tag 0F7J
(auxiliary; not a blueprint node).
Proof: identify the formalism's triangle compositor with the actual proper/open tower
map, using the exact-derived open compositor and the canonical right-derived proper
compositor. Its every-triangle equation then gives the result for the supplied tower. -/
private lemma unbounded_sh_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (unboundedFormalism A).shId X =
      Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫ Functor.mapDerivedCategoryIdIso _ := by
  rw [ExchangeFormalism.shId]
  apply conjugate_iso_symm_eq
  exact derived_open_id_conjugate A X

private lemma unbounded_pf_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (unboundedFormalism A).pfId X =
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
          Functor.mapDerivedCategoryIdIso _ := by
  exact derived_star_id_conjugate A X

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange

section BoundedBelowRestriction

open Abelian

section Proper
attribute [local irreducible] upperStarLowerStarAdjunction
  mapDerivedUpperStarLowerStarAdjunction Adjunction.derivedPlus
  Adjunction.mapDerivedCategoryAdjunction Adjunction.mapDerivedCategoryPlusAdjunction

attribute [local irreducible] upperStar lowerStar
section ProperExchangeRestriction
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.rightDerivedFunctorPlusCompatibility
end ProperExchangeRestriction
end Proper
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorPlusCompatibility
section ExchangeRestriction

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryPlusAdjunction upperStarLowerStarAdjunction
  mapDerivedUpperStarLowerStarAdjunction Adjunction.derivedPlus
  Adjunction.mapDerivedCategoryAdjunction
end ExchangeRestriction

section CompositionRestriction

-- Keep the sheaf adjunction abstract while comparing its derived units.
attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction

section BoundedOpenCompositor
attribute [local irreducible] Adjunction.mapDerivedCategoryPlusAdjunction
  upperStarLowerStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  Adjunction.derivedPlus Adjunction.mapDerivedCategoryAdjunction

end BoundedOpenCompositor

end CompositionRestriction

end BoundedBelowRestriction

open CategoryTheory.Abelian
section NormalizationModels
universe w₁ w₂ v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  [HasKInjectiveResolutions C]
universe w₃ v₃ u₃
variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
end NormalizationModels
section NormalizationRefinements
attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

end NormalizationRefinements

end AlgebraicGeometry.Etale
