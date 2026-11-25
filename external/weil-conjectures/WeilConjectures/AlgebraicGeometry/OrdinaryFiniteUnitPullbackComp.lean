/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle

/-! # Constant-object pullback comparisons

Source: blueprint vector integration, compatibility with restriction.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor upperStar

private theorem single_comp (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    (hw : w = p ≫ v) (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj P) ≫
      (ordinaryFinitePullback A p).map
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).hom.app P) ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) p).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).obj P) =
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) w).hom.app P ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app P) := by
  exact leftDerivedUpperStarComp_hom_app_singleFunctor (ModuleCat.{u + 1} A) p v w hw P

private theorem single_comp_maps
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (R : D₀ ⥤ D₂)
    (sF : E₀ ⋙ P ≅ F ⋙ E₁) (sG : E₁ ⋙ Q ≅ G ⋙ E₂)
    (sH : E₀ ⋙ R ≅ H ⋙ E₂) (c : R ≅ P ⋙ Q) (k : H ≅ F ⋙ G)
    (X₀ : C₀) (X₁ : C₁) (X₂ : C₂)
    (a : F.obj X₀ ⟶ X₁) (b : G.obj X₁ ⟶ X₂) (d : H.obj X₀ ⟶ X₂)
    (hc : c.hom.app (E₀.obj X₀) ≫ Q.map (sF.hom.app X₀) ≫
        sG.hom.app (F.obj X₀) = sH.hom.app X₀ ≫ E₂.map (k.hom.app X₀))
    (hd : k.hom.app X₀ ≫ G.map a ≫ b = d) :
    c.hom.app (E₀.obj X₀) ≫ Q.map (sF.hom.app X₀ ≫ E₁.map a) ≫
        sG.hom.app X₁ ≫ E₂.map b = sH.hom.app X₀ ≫ E₂.map d := by
  have hn := sG.hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hc]
  simp only [← E₂.map_comp, hd]

private theorem unit_comp_rfl (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v (p ≫ v) rfl).hom.app
        (ordinaryFiniteUnit A S) ≫
      (ordinaryFinitePullback A p).map (ordinaryFiniteUnitPullback A v).hom ≫
      (ordinaryFiniteUnitPullback A p).hom = (ordinaryFiniteUnitPullback A (p ≫ v)).hom := by
  rw [ordinaryFiniteUnitPullback_hom A v, ordinaryFiniteUnitPullback_hom A p,
    ordinaryFiniteUnitPullback_hom A (p ≫ v)]
  exact single_comp_maps
    (_root_.DerivedCategory.singleFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (_root_.DerivedCategory.singleFunctor
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (_root_.DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (upperStar (ModuleCat.{u + 1} A) v) (upperStar (ModuleCat.{u + 1} A) p)
    (upperStar (ModuleCat.{u + 1} A) (p ≫ v))
    (ordinaryFinitePullback A v) (ordinaryFinitePullback A p)
    (ordinaryFinitePullback A (p ≫ v))
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) p)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) (p ≫ v))
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v)
    (upperStarComp (ModuleCat.{u + 1} A) p v)
    (ordinaryFiniteConstant A S) (ordinaryFiniteConstant A U) (ordinaryFiniteConstant A T)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app (ModuleCat.of A A))
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).hom.app (ModuleCat.of A A))
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (p ≫ v)).hom.app
      (ModuleCat.of A A))
    (single_comp A p v (p ≫ v) rfl (ordinaryFiniteConstant A S))
    (Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A) p v (ModuleCat.of A A))

/-- The actual constant-object comparisons respect derived pullback composition.
Source: blueprint vector integration, restriction compatibility; composition of
upperStarConstantSheafIso and derived pullback on degree-zero sheaves.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteUnitPullback_comp (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    (hw : w = p ≫ v) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app
        (ordinaryFiniteUnit A S) ≫
      (ordinaryFinitePullback A p).map (ordinaryFiniteUnitPullback A v).hom ≫
      (ordinaryFiniteUnitPullback A p).hom = (ordinaryFiniteUnitPullback A w).hom := by
  subst w
  exact unit_comp_rfl A p v

end AlgebraicGeometry.Etale
