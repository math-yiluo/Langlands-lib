/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.Etale.Quotient.EtaleQuotientTensorProjectionProperFactor
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData

import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantPullbackComposition

import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenRestrictedTensorProjection
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarConstantCoefficientIso
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric

/-! # Open-factor pasting for the restricted coefficient projection

This assembly step pastes the proper mate projection square with the open
restriction and constant-tensor comparison. It is stated conditionally on the
proper mate square so that the unbounded mate calculation is an independent
intermediate result.
(blueprint: lem-pur-etale-quotient-tensor-projection-open-pasting)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry.Etale

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

section
attribute [local instance] Sheaf.monoidalCategory

private theorem derivedSymmetry_swap
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) (K L : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((derivedTensorSymmetry A T).inv.app K).app L =
      ((derivedTensorSymmetry A T).hom.app L).app K := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf T.smallEtaleTopology A)
  exact (SymmetricCategory.braiding_swap_eq_inv_braiding K L).symm

end

private theorem coefficient_comparison_hom
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    (W : Scheme.{u}) (L : DerivedCategoryModule C W) :
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  let b := etaleScalarConstantCoefficientIso a
  ((scalarTensorIso a W).app L ≪≫
      ((derivedTensor (ModuleCat.{u + 1} C) W).obj L).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((constantCommuteCompose W.smallEtaleTopology
            (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
          (Functor.mapDerivedCategorySingleFunctor
            (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
              ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) ≪≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) W).app L).app
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)).hom =
    (scalarTensorIso a W).hom.app L ≫
      ((derivedTensor (ModuleCat.{u + 1} C) W).obj L).map (b W).hom ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) W).hom.app L).app
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)
    := by rfl

/-- Defining components of the generic projection constructor. -/
private theorem projection_construction_components
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {D₀ : Type*} [Category D₀] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : D₀ ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (H' : D₀ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : H ⋙ (upperStar A f).leftDerivedFunctor ≅ H') (V : D₀)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    exceptionalProjectionConstruction A c H H' t V K =
      ((derivedTensorSymmetry A Y).hom.app (H.obj V)).app
          ((rightDerivedLowerShriekOfCompactification A c).obj K) ≫
        ((projectionMapOfCompactification A c).app K).app (H.obj V) ≫
        (rightDerivedLowerShriekOfCompactification A c).map
          (((derivedTensor A X).obj K).map (t.hom.app V) ≫
            ((derivedTensorSymmetry A X).hom.app K).app (H'.obj V)) := by
  rfl

/-- The specified constant projection has its three defining components.
Source: Zheng, Construction 2.26; expand the generic projection constructor. -/
private theorem constant_projection_components
    (C : Type (u + 1)) [CommRing C]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (V : DerivedCategory (ModuleCat.{u + 1} C)) (K : DerivedCategoryModule C X) :
    exceptionalConstantProjectionMap C c V K =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).hom.app
        ((constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)).app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app
        ((constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
        (((derivedTensor (ModuleCat.{u + 1} C) X).obj K).map
            ((exceptionalConstantPullbackIso C f).hom.app V) ≫
          ((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).hom.app K).app
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)) := by
  exact projection_construction_components (ModuleCat.{u + 1} C) c
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory
    (exceptionalConstantPullbackIso C f) V K

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedTensor upperStar lowerStar
  HasDerivedCategory.standard
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategorySingleFunctor
  singleFunctorCompLeftDerivedUpperStarIso leftDerivedUpperStarComp
  leftDerivedUpperStarCompactificationIso exceptionalConstantPullbackIso
  scalarTensorIso scalarCoefficientPullbackIso derivedTensorSymmetry

attribute [local irreducible] rightDerivedLowerStarProjectionMap
  derivedOpenImmersionLowerShriekProjectionIso openImmersionLowerShriek

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private theorem derivedSymmetry_involutive
    (C : Type (u + 1)) [CommRing C] (Y : Scheme.{u})
    (K L : DerivedCategoryModule C Y) :
    ((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).hom.app K).app L ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} C) Y).hom.app L).app K = 𝟙 _ := by
  rw [← derivedSymmetry_swap (ModuleCat.{u + 1} C) Y K L]
  exact congr_app (Iso.hom_inv_id_app
    (derivedTensorSymmetry (ModuleCat.{u + 1} C) Y) K) L

private theorem projection_pasting
    {E : Type*} [Category E]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ C₀ C₁ C₂ C₃ C₄ : E}
    {z₁ : A₀ ⟶ A₁} {z₂ : A₁ ⟶ A₂} {s : A₂ ⟶ A₃}
    {b : A₃ ⟶ C₄} {σ : A₀ ⟶ B₀} {p : B₀ ⟶ B₁}
    {t₁ : B₁ ⟶ B₂} {t₂ : B₂ ⟶ B₃} {t₃ : B₃ ⟶ A₃}
    {t : B₁ ⟶ C₁} {byMap : B₀ ⟶ C₀} {pH : C₀ ⟶ C₁}
    {q₁ : C₁ ⟶ C₂} {q₂ : C₂ ⟶ C₃} {q₃ : C₃ ⟶ C₄}
    (h₁ : z₁ ≫ z₂ ≫ s = σ ≫ p ≫ t₁ ≫ t₂ ≫ t₃)
    (h₂ : t₁ ≫ t₂ ≫ t₃ ≫ b = t ≫ q₁ ≫ q₂ ≫ q₃)
    (hn : byMap ≫ pH = p ≫ t) :
    z₁ ≫ z₂ ≫ s ≫ b = σ ≫ byMap ≫ pH ≫ q₁ ≫ q₂ ≫ q₃ := by
  rw [reassoc_of% h₁, h₂, ← reassoc_of% hn]

/-- The untwisted constant-coefficient projection word.
Source: Zheng, Proposition 2.29(2), Construction 2.26. Paste the proper mate
hypothesis with the open projection identity, transport the coefficient by
naturality, and combine constant pullback along the two compactification factors. -/
private theorem compact_projection_word
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X)
    (hproper :
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
          ((scalarMate a c.g).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        (scalarRestrictionDirectImageMap a c.g).app
          ((scalarExtension a c.Z).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) =
      (scalarTensorIso a Y).hom.app
          ((lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) c.g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).app
          (scalarCoefficient a Y) ≫
        (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} C) c.Z).obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).map
              (scalarCoefficientPullbackIso a c.g).hom ≫
            (scalarTensorIso a c.Z).inv.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K))) :
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory
  let G := (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor
  let RY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a
  RY.map ((compactScalarMap a c).app K) ≫
    (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
      ((scalarExtension a X).obj K) ≫
    G.map (J.map ((scalarTensorIso a X).hom.app K)) =
  (scalarTensorIso a Y).hom.app (G.obj (J.obj K)) ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) c.g).app
      (J.obj K)).app (scalarCoefficient a Y) ≫
    G.map (((derivedTensor (ModuleCat.{u + 1} C) c.Z).obj (J.obj K)).map
      (scalarCoefficientPullbackIso a c.g).hom) ≫
    G.map (((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} C) c.i).inv.app K).app (scalarCoefficient a c.Z)) ≫
    G.map (J.map (((derivedTensor (ModuleCat.{u + 1} C) X).obj K).map
      (scalarCoefficientPullbackIso a c.i).hom)) := by
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory
  let G := (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor
  let RZ := Sheaf.derivedRestrictScalars c.Z.smallEtaleTopology a
  let RY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a
  have hop := etaleOpenRestrictedTensorProjection a c.i K
  have hn := (scalarRestrictionDirectImageMap a c.g).naturality
    ((ExceptionalCoefficients.openIso a c.i).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  as_aux_lemma =>
    dsimp only [RY, RZ, G, J]
    simp only [compactScalarMap_proper_open_factor, Functor.map_comp,
      CommRingCat.hom_ofHom,
      SystemProjection.singleRestriction, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc]
    erw [reassoc_of% hn]
    rw [← Category.assoc, ← Category.assoc]
    erw [hproper]
    simp only [Functor.map_comp, Category.assoc]
    have hp := congrArg G.map hop
    simp only [Functor.map_comp] at hp
    dsimp only [G, J] at hp
    erw [hp]

private theorem map_pair
    {E F : Type*} [Category E] [Category F] (T : E ⥤ F)
    {A B C D : E} {l : A ⟶ B} {m : B ⟶ D} {r : A ⟶ C} {s : C ⟶ D}
    (h : l ≫ m = r ≫ s) : T.map l ≫ T.map m = T.map r ≫ T.map s := by
  rw [← T.map_comp, h, T.map_comp]

private theorem map_pair_twice
    {E F G : Type*} [Category E] [Category F] [Category G] (J : F ⥤ G) (T : E ⥤ F)
    {A B C D : E} {l : A ⟶ B} {m : B ⟶ D} {r : A ⟶ C} {s : C ⟶ D}
    (h : l ≫ m = r ≫ s) :
    J.map (T.map l) ≫ J.map (T.map m) = J.map (T.map r) ≫ J.map (T.map s) := by
  exact map_pair J (map_pair T h)

/-- Functorial transport of constant pullback composition.
Source: Zheng, Construction 2.26. Apply preservation of composition first to
T and then to J in the proved degree-zero constant pullback equation. -/
private theorem mapped_constant_composition
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C)
    (T : DerivedCategoryModule C X ⥤ DerivedCategoryModule C X)
    (J : DerivedCategoryModule C X ⥤ DerivedCategoryModule C c.Z) :
    J.map (T.map ((upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((exceptionalConstantPullbackIso C c.g).hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)))) ≫
      J.map (T.map ((exceptionalConstantPullbackIso C c.i).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M))) =
    J.map (T.map ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)))) ≫
      J.map (T.map ((exceptionalConstantPullbackIso C f).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M))) := by
  exact map_pair_twice J T (etaleConstantPullback_comp_single C c M)

private theorem coefficient_tail
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X) :
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory
  let TX := (derivedTensor (ModuleCat.{u + 1} C) X).obj K
  let TZ := (derivedTensor (ModuleCat.{u + 1} C) c.Z).obj (J.obj K)
  let Pg := (upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  let HY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V
  let O := (derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} C) c.i).inv.app K
  TZ.map (scalarCoefficientPullbackIso a c.g).hom ≫ O.app (scalarCoefficient a c.Z) ≫
      J.map (TX.map (scalarCoefficientPullbackIso a c.i).hom) ≫
      J.map (TX.map ((etaleScalarConstantCoefficientIso a) X).hom) =
    TZ.map (Pg.map ((etaleScalarConstantCoefficientIso a) Y).hom) ≫ O.app (Pg.obj HY) ≫
      J.map (TX.map ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C)
        c).hom.app HY)) ≫
      J.map (TX.map ((exceptionalConstantPullbackIso C f).hom.app V)) := by
  dsimp only
  have hcomp := etaleConstantPullback_comp_single C c
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  have hg₀ := (etaleScalarConstantCoefficientIso_pullback a c.g).symm
  have hi₀ := (etaleScalarConstantCoefficientIso_pullback a c.i).symm
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory
  let G := (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor
  let TX := (derivedTensor (ModuleCat.{u + 1} C) X).obj K
  let TZ := (derivedTensor (ModuleCat.{u + 1} C) c.Z).obj (J.obj K)
  let TY := (derivedTensor (ModuleCat.{u + 1} C) Y).obj (G.obj (J.obj K))
  let Pi := (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor
  let Pg := (upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor
  let O := (derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} C) c.i).inv.app K
  have ho (L L' : DerivedCategoryModule C c.Z) (h : L ⟶ L') :
      TZ.map h ≫ O.app L' = O.app L ≫ J.map (TX.map (Pi.map h)) := by
    as_aux_lemma => exact O.naturality h
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  let Qg := (exceptionalConstantPullbackIso C c.g).hom.app V
  let Qi := (exceptionalConstantPullbackIso C c.i).hom.app V
  let Qf := (exceptionalConstantPullbackIso C f).hom.app V
  let L := ((constantSheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)
  have h2 :
      TZ.map (scalarCoefficientPullbackIso a c.g).hom ≫
        TZ.map (etaleScalarConstantCoefficientIso a c.Z).hom =
      TZ.map (Pg.map (etaleScalarConstantCoefficientIso a Y).hom) ≫ TZ.map Qg := by
    as_aux_lemma => exact map_pair TZ hg₀
  have h3 : TZ.map Qg ≫ O.app _ =
      O.app (Pg.obj L) ≫ J.map (TX.map (Pi.map Qg)) := by
    as_aux_lemma => exact ho _ _ Qg
  have h4 := mapped_constant_composition C c
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)) TX J
  have hi' :
      J.map (TX.map (scalarCoefficientPullbackIso a c.i).hom) ≫
        J.map (TX.map (etaleScalarConstantCoefficientIso a X).hom) =
      J.map (TX.map (Pi.map (etaleScalarConstantCoefficientIso a c.Z).hom)) ≫
        J.map (TX.map Qi) := by
    as_aux_lemma => exact map_pair_twice J TX hi₀
  as_aux_lemma =>
    rw [hi', reassoc_of% (ho _ _ (etaleScalarConstantCoefficientIso a c.Z).hom).symm,
      reassoc_of% h2, reassoc_of% h3, h4]

private theorem proper_coefficient_naturality
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (M : DerivedCategoryModule C Z) :
  let b := etaleScalarConstantCoefficientIso a
  let G := (lowerStar (ModuleCat.{u + 1} C) g).rightDerivedFunctor
  let Pg := (upperStar (ModuleCat.{u + 1} C) g).leftDerivedFunctor
  let TY := (derivedTensor (ModuleCat.{u + 1} C) Y).obj (G.obj M)
  let TZ := (derivedTensor (ModuleCat.{u + 1} C) Z).obj M
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  let HY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V
  TY.map (b Y).hom ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) g).app M).app HY =
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) g).app M).app
        (scalarCoefficient a Y) ≫ G.map (TZ.map (Pg.map (b Y).hom)) := by
  dsimp only
  exact ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) g).app M).naturality
    (etaleScalarConstantCoefficientIso a Y).hom

private theorem constant_projection_pre
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X)
    (hproper :
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
          ((scalarMate a c.g).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        (scalarRestrictionDirectImageMap a c.g).app
          ((scalarExtension a c.Z).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) =
      (scalarTensorIso a Y).hom.app
          ((lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) c.g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).app
          (scalarCoefficient a Y) ≫
        (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} C) c.Z).obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).map
              (scalarCoefficientPullbackIso a c.g).hom ≫
            (scalarTensorIso a c.Z).inv.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K))) :
  let RY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a
  let b := etaleScalarConstantCoefficientIso a
  let TX := (derivedTensor (ModuleCat.{u + 1} C) X).obj K
  let TY := (derivedTensor (ModuleCat.{u + 1} C) Y).obj
    ((lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K))
  let _Qf := (exceptionalConstantPullbackIso C f).hom.app ((DerivedCategory.singleFunctor
    (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)))
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory
  let G := (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor
  let Pg := (upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor
  let O := (derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} C) c.i).inv.app K
  RY.map ((compactScalarMap a c).app K) ≫
      (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
        ((scalarExtension a X).obj K) ≫
      G.map (J.map ((scalarTensorIso a X).hom.app K ≫ TX.map (b X).hom)) =
    (scalarTensorIso a Y).hom.app (G.obj (J.obj K)) ≫ TY.map (b Y).hom ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) c.g).app
        (J.obj K)).app (((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
          C)).mapDerivedCategory.obj ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C)
          0).obj
((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))))) ≫
      G.map (O.app (Pg.obj (((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        C)).mapDerivedCategory.obj ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))))))) ≫
      G.map (J.map (TX.map ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C)
        c).hom.app
(((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
  ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)))))))) ≫ G.map (J.map (TX.map
  (((exceptionalConstantPullbackIso C f).hom.app ((DerivedCategory.singleFunctor
  (ModuleCat.{u + 1} C) 0).obj
((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))))))) := by
  dsimp only
  let b := etaleScalarConstantCoefficientIso a
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory
  let G := (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor
  let TX := (derivedTensor (ModuleCat.{u + 1} C) X).obj K
  let TZ := (derivedTensor (ModuleCat.{u + 1} C) c.Z).obj (J.obj K)
  let Pi := (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor
  let Pg := (upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor
  let O := (derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} C) c.i).inv.app K
  have hcompact := compact_projection_word a c K hproper
  have hh := congrArg G.map (coefficient_tail a c K)
  simp only [Functor.map_comp] at hh
  have hp := proper_coefficient_naturality a c.g (J.obj K)
  simp only [Functor.map_comp]
  exact projection_pasting hcompact hh hp

private theorem constant_projection_word
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X)
    (hproper :
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
          ((scalarMate a c.g).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        (scalarRestrictionDirectImageMap a c.g).app
          ((scalarExtension a c.Z).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) =
      (scalarTensorIso a Y).hom.app
          ((lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) c.g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).app
          (scalarCoefficient a Y) ≫
        (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} C) c.Z).obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).map
              (scalarCoefficientPullbackIso a c.g).hom ≫
            (scalarTensorIso a c.Z).inv.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K))) :
  let RY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a
  let b := etaleScalarConstantCoefficientIso a
  let TX := (derivedTensor (ModuleCat.{u + 1} C) X).obj K
  let TY := (derivedTensor (ModuleCat.{u + 1} C) Y).obj ((rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} C) c).obj K)
  let Qf := (exceptionalConstantPullbackIso C f).hom.app ((DerivedCategory.singleFunctor
    (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)))
  RY.map ((compactScalarMap a c).app K) ≫
      (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
        ((scalarExtension a X).obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map ((scalarTensorIso a
        X).hom.app K ≫ TX.map (b X).hom) =
    (scalarTensorIso a Y).hom.app ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C)
      c).obj K) ≫ TY.map (b Y).hom ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app (((constantSheaf
        Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))))) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map (TX.map Qf) := by
  let RY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory
  let G := (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor
  let Pg := (upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor
  let O := (derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} C) c.i).inv.app K
  let b := etaleScalarConstantCoefficientIso a
  let TX := (derivedTensor (ModuleCat.{u + 1} C) X).obj K
  let TZ := (derivedTensor (ModuleCat.{u + 1} C) c.Z).obj (J.obj K)
  let TY := (derivedTensor (ModuleCat.{u + 1} C) Y).obj (G.obj (J.obj K))
  have hpre := constant_projection_pre a c K hproper
  have hconstant :
      RY.map ((compactScalarMap a c).app K) ≫
          (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
            ((scalarExtension a X).obj K) ≫
          G.map (J.map ((scalarTensorIso a X).hom.app K ≫ TX.map (b X).hom)) =
        (scalarTensorIso a Y).hom.app (G.obj (J.obj K)) ≫ TY.map (b Y).hom ≫
          ((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app (((constantSheaf
            Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))))) ≫
          G.map (J.map (TX.map (((exceptionalConstantPullbackIso C f).hom.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))))))) := by
    dsimp only [TY, TX, Pg, O] at hpre ⊢
    rw [projectionMapOfCompactification_app_app]
    simpa only [Functor.map_comp, Category.assoc] using hpre
  exact hconstant

/-- Paste the open restriction comparison and the constant tensor maps after a
proper mate projection identity.
Source: Zheng, Proposition 2.29(2), Construction 2.26; Stacks Tag 0GL6.
(blueprint: lem-pur-etale-quotient-tensor-projection-open-pasting).

Proof: use naturality of the open coefficient comparison and of the restriction
mate, then expand the two signed tensor symmetries. The resulting composite is
the defining `exceptionalConstantProjectionMap`.
-/
theorem etaleQuotientTensorProjection_of_proper_mate
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X)
    (hproper :
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
          ((scalarMate a c.g).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        (scalarRestrictionDirectImageMap a c.g).app
          ((scalarExtension a c.Z).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) =
      (scalarTensorIso a Y).hom.app
          ((lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} C) c.g).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).app
          (scalarCoefficient a Y) ≫
        (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} C) c.Z).obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)).map
              (scalarCoefficientPullbackIso a c.g).hom ≫
            (scalarTensorIso a c.Z).inv.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K))) :
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  let e (W : Scheme.{u}) (L : DerivedCategoryModule C W) :=
    (scalarTensorIso a W).app L ≪≫
      ((derivedTensor (ModuleCat.{u + 1} C) W).obj L).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((constantCommuteCompose W.smallEtaleTopology
            (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
          (Functor.mapDerivedCategorySingleFunctor
            (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
              ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) ≪≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) W).app L).app
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)
  (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
      ((compactScalarMap a c).app K) ≫
    (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
      ((scalarExtension a X).obj K) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
      (e X K).hom =
  (e Y ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)).hom ≫
    exceptionalConstantProjectionMap C c V K := by
  have hraw := constant_projection_word a c K hproper
  dsimp only at hraw ⊢
  let RY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology a
  let b := etaleScalarConstantCoefficientIso a
  let TX := (derivedTensor (ModuleCat.{u + 1} C) X).obj K
  let TY := (derivedTensor (ModuleCat.{u + 1} C) Y).obj ((rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} C) c).obj K)
  let Qf := (exceptionalConstantPullbackIso C f).hom.app ((DerivedCategory.singleFunctor
    (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)))
  let sigX := (((derivedTensorSymmetry (ModuleCat.{u + 1} C) X).hom.app K).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
            ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)))))
  have hh := eq_whisker hraw
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map sigX)
  trans (RY.map ((compactScalarMap a c).app K) ≫
      (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
        ((scalarExtension a X).obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map ((scalarTensorIso a
        X).hom.app K ≫ TX.map (b X).hom)) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map sigX
  · dsimp only [RY, b, TX, TY, Qf, sigX]
    as_aux_lemma =>
      rw [coefficient_comparison_hom a X K]
      simp only [Functor.map_comp, Category.assoc]
  trans ((scalarTensorIso a Y).hom.app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K) ≫
      TY.map (b Y).hom ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} C) c).app K).app (((constantSheaf
        Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))))) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map (TX.map Qf)) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map sigX
  · exact hh
  · dsimp only [RY, b, TX, TY, Qf, sigX]
    as_aux_lemma =>
      rw [coefficient_comparison_hom a Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K),
        constant_projection_components]
      simp only [Functor.map_comp, Category.assoc]
      erw [reassoc_of% (derivedSymmetry_involutive C Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
            ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)))))]

end AlgebraicGeometry.Etale
