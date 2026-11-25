/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantPullbackSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Derived inverse-image composition on single objects -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedTensor upperStar lowerStar
  HasDerivedCategory.standard
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategorySingleFunctor
  singleFunctorCompLeftDerivedUpperStarIso leftDerivedUpperStarComp
  leftDerivedUpperStarCompactificationIso exceptionalConstantPullbackIso

private theorem single_comp_pasting
    {A B E A' B' E' : Type*}
    [Category A] [Category B] [Category E] [Category A'] [Category B'] [Category E']
    (Fg : A ⥤ B) (Fi : B ⥤ E) (Ff : A ⥤ E)
    (Pg : A' ⥤ B') (Pi : B' ⥤ E') (Pf : A' ⥤ E')
    (SA : A ⥤ A') (SB : B ⥤ B') (SE : E ⥤ E')
    (dg : SA ⋙ Pg ⟶ Fg ⋙ SB) (di : SB ⋙ Pi ⟶ Fi ⋙ SE)
    (df : SA ⋙ Pf ⟶ Ff ⋙ SE) (lc : Pf ≅ Pg ⋙ Pi) (oc : Ff ⟶ Fg ⋙ Fi)
    (W : A) (Z : B) (T : E)
    (cg : Fg.obj W ⟶ Z) (ci : Fi.obj Z ⟶ T) (cf : Ff.obj W ⟶ T)
    (hk : lc.hom.app (SA.obj W) ≫ Pi.map (dg.app W) ≫ di.app (Fg.obj W) =
      df.app W ≫ SE.map (oc.app W))
    (ho : oc.app W ≫ Fi.map cg ≫ ci = cf) :
    Pi.map (dg.app W ≫ SB.map cg) ≫ di.app Z ≫ SE.map ci =
      lc.inv.app (SA.obj W) ≫ df.app W ≫ SE.map cf := by
  rw [← cancel_epi (lc.hom.app (SA.obj W)), Iso.hom_inv_id_app_assoc]
  have hn := di.naturality cg
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hk]
  rw [← SE.map_comp_assoc, ← SE.map_comp, Category.assoc, ho]

private theorem pullbackSingle_key
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (W : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)) :
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} C) c.i c.g f c.comm).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj W) ≫
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
      ((singleFunctorCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} C) c.g).hom.app W) ≫
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) c.i).hom.app
      ((upperStar (ModuleCat.{u + 1} C) c.g).obj W) =
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app W ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} C) c.i c.g f c.comm).hom.app W) := by
  simp only [leftDerivedUpperStarComp, singleFunctorCompLeftDerivedUpperStarIso,
    Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj,
    Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj]

/-- The composition comparison for derived inverse image acts on single objects by
ordinary inverse-image composition, including arbitrary compatible coefficient maps.
Source: Stacks Tag 07A6 and derived pullback composition
(blueprint: lem-pur-etale-constant-pullback-native).
Proof: expand the derived composition and its comparison on single objects.
Naturality moves the first coefficient map through the second single comparison.
Functoriality then identifies the composite with the given ordinary composition. -/
theorem etaleConstantPullback_single_native
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (W : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C))
    (Z : Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} C))
    (T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C))
    (cg : (upperStar (ModuleCat.{u + 1} C) c.g).obj W ⟶ Z)
    (ci : (upperStar (ModuleCat.{u + 1} C) c.i).obj Z ⟶ T)
    (cf : (upperStar (ModuleCat.{u + 1} C) f).obj W ⟶ T)
    (ho : (upperStarComp (ModuleCat.{u + 1} C) c.i c.g f c.comm).hom.app W ≫
      (upperStar (ModuleCat.{u + 1} C) c.i).map cg ≫ ci = cf) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((singleFunctorCompLeftDerivedUpperStarIso
          (ModuleCat.{u + 1} C) c.g).hom.app W ≫
          (DerivedCategory.singleFunctor _ 0).map cg) ≫
      (singleFunctorCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} C) c.i).hom.app Z ≫
      (DerivedCategory.singleFunctor _ 0).map ci =
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj W) ≫
      (singleFunctorCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} C) f).hom.app W ≫
      (DerivedCategory.singleFunctor _ 0).map cf := by
  rw [leftDerivedUpperStarCompactificationIso_eq, Iso.symm_hom]
  exact single_comp_pasting
    (upperStar (ModuleCat.{u + 1} C) c.g) (upperStar (ModuleCat.{u + 1} C) c.i)
    (upperStar (ModuleCat.{u + 1} C) f)
    (upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (DerivedCategory.singleFunctor _ 0)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) c.g).hom
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) c.i).hom
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} C) c.i c.g f c.comm)
    (upperStarComp (ModuleCat.{u + 1} C) c.i c.g f c.comm).hom
    W Z T cg ci cf (pullbackSingle_key C c W) ho

private theorem inverse_conjugate
    {A B : Type*} [Category A] [Category B] (P : A ⥤ B)
    {Y Y' : A} {X X' : B} (ay : Y ⟶ Y') (ay' : Y' ⟶ Y)
    (hy : ay ≫ ay' = 𝟙 Y) (ax : X ⟶ X')
    (q : P.obj Y ⟶ X) (d : P.obj Y' ⟶ X')
    (h : P.map ay' ≫ q ≫ ax = d) :
    q ≫ ax = P.map ay ≫ d := by
  rw [← h, ← P.map_comp_assoc, hy, P.map_id, Category.id_comp]

private theorem ordinaryConstant_comp
    (C : Type (u + 1)) [CommRing C] {X Z Y : Scheme.{u}}
    (i : X ⟶ Z) (g : Z ⟶ Y) (f : X ⟶ Y) (hf : f = i ≫ g)
    (M : ModuleCat.{u + 1} C) :
    (upperStarComp (ModuleCat.{u + 1} C) i g f hf).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M) ≫
      (upperStar (ModuleCat.{u + 1} C) i).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) g).hom.app M) ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) i).hom.app M =
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) f).hom.app M := by
  subst f
  exact Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} C) i g M

private theorem constantPullback_single_forward
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} C) :
    (exceptionalConstantPullbackIso C f).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M) ≫
      ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} C)).mapDerivedCategorySingleFunctor 0).hom.app M =
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.map
        (((constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) f).hom.app M) := by
  exact inverse_conjugate _ _ _ (Iso.hom_inv_id_app _ M) _ _ _
    (etaleConstantPullback_single C f M)

private def constantSingleMap
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M) :=
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M) ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) f).hom.app M)

private def constantSingleHom
    (C : Type (u + 1)) [CommRing C] (X : Scheme.{u})
    (M : ModuleCat.{u + 1} C) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M) :=
  ((constantSheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} C)).mapDerivedCategorySingleFunctor 0).hom.app M

private def constantDerivedMap
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M) :=
  (exceptionalConstantPullbackIso C f).hom.app
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)

private theorem constantSingleMap_eq
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} C) :
    constantSingleMap C f M =
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M) ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) f).hom.app M) := by
  rfl

private theorem constantSingleHom_eq
    (C : Type (u + 1)) [CommRing C] (X : Scheme.{u})
    (M : ModuleCat.{u + 1} C) :
    constantSingleHom C X M =
  ((constantSheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} C)).mapDerivedCategorySingleFunctor 0).hom.app M := by
  rfl

private theorem constantDerivedMap_eq
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} C) :
    constantDerivedMap C f M =
  (exceptionalConstantPullbackIso C f).hom.app
    ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M) := by
  rfl

private theorem constantForward
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ModuleCat.{u + 1} C) :
    constantDerivedMap C f M ≫ constantSingleHom C X M =
      (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.map
        (constantSingleHom C Y M) ≫ constantSingleMap C f M := by
  simp only [constantDerivedMap_eq, constantSingleHom_eq, constantSingleMap_eq]
  exact constantPullback_single_forward C f M

private theorem map_forward_pair
    {E F : Type*} [Category E] [Category F] (P : E ⥤ F)
    {A B C D : E} {T U : F}
    {q : A ⟶ B} {b : B ⟶ D} {a : A ⟶ C} {d : C ⟶ D}
    {r : P.obj B ⟶ T} {ax : T ⟶ U} {di : P.obj D ⟶ U}
    (hg : q ≫ b = a ≫ d) (hi : r ≫ ax = P.map b ≫ di) :
    P.map q ≫ r ≫ ax = P.map a ≫ P.map d ≫ di := by
  rw [hi, ← P.map_comp_assoc, hg, P.map_comp, Category.assoc]

private theorem step_one
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        (constantDerivedMap C c.g M) ≫ constantDerivedMap C c.i M ≫
        constantSingleHom C X M =
      (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor.map
          (constantSingleHom C Y M)) ≫
        (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
          (constantSingleMap C c.g M) ≫ constantSingleMap C c.i M := by
  exact map_forward_pair _
    (constantForward C c.g M) (constantForward C c.i M)

private theorem step_two
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        (constantSingleMap C c.g M) ≫ constantSingleMap C c.i M =
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)) ≫
        constantSingleMap C f M := by
  simp only [constantSingleMap_eq]
  exact etaleConstantPullback_single_native C c
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)
    ((constantSheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) c.g).hom.app M)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) c.i).hom.app M)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) f).hom.app M)
    (ordinaryConstant_comp C c.i c.g f c.comm M)

private theorem singleHom_naturality
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor.map
          (constantSingleHom C Y M)) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)) =
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ≫
      (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.map
        (constantSingleHom C Y M) := by
  exact (leftDerivedUpperStarCompactificationIso
    (ModuleCat.{u + 1} C) c).hom.naturality (constantSingleHom C Y M)

private theorem triple_transport
    {E : Type*} [Category E] {A B C D F : E}
    {r : A ⟶ B} {lc : B ⟶ C} {d : C ⟶ D}
    {lc₀ : A ⟶ F} {rf : F ⟶ C} {q : F ⟶ D}
    (hn : r ≫ lc = lc₀ ≫ rf) (hf : q = rf ≫ d) :
    r ≫ lc ≫ d = lc₀ ≫ q := by
  rw [hf, ← Category.assoc, hn, Category.assoc]

private theorem step_three
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor.map
          (constantSingleHom C Y M)) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)) ≫
      constantSingleMap C f M =
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ≫
        constantDerivedMap C f M ≫ constantSingleHom C X M := by
  have hf := constantForward C f M
  exact triple_transport (singleHom_naturality C c M) hf

private instance constantSingleHom_isIso
    (C : Type (u + 1)) [CommRing C] (X : Scheme.{u})
    (M : ModuleCat.{u + 1} C) : IsIso (constantSingleHom C X M) := by
  unfold constantSingleHom
  infer_instance

end AlgebraicGeometry.Etale
