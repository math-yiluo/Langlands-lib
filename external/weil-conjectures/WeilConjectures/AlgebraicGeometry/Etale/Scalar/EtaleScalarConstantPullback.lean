/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
import WeilConjectures.AlgebraicGeometry.Etale.EtaleOrdinaryConstantRestriction
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantPullbackSingle
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.Tactic.TransportExact

/-! # Pullback of the constant scalar coefficient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory Functor.rightDerivedFunctor
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

private theorem ordinaryConstant_unit
    (D : Type (u + 1)) [CommRing D] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} D) f).hom.app
        (ModuleCat.of D D) =
      (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} D) f)).inv := by
  rw [Functor.Monoidal.εIso_inv]
  exact upperStarConstantSheafIso_hom_app_tensorUnit (ModuleCat.{u + 1} D) f

private def coefficientConstantMap
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    (W : Scheme.{u}) : scalarCoefficientSheaf a W ⟶
    (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).obj
      ((ModuleCat.restrictScalars.{u + 1} a).obj (ModuleCat.of D D)) :=
  (constantCommuteCompose W.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} a)).hom.app (ModuleCat.of D D)

private theorem coefficientConstantMap_pullback
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} C) f).map (coefficientConstantMap a Y) ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} C) f).hom.app
        ((ModuleCat.restrictScalars.{u + 1} a).obj (ModuleCat.of D D)) =
    (upperStarRestrictScalarsIsoSheaf a f).hom.app
        (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D))) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology a).map
        (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} D) f)).inv ≫
      coefficientConstantMap a X := by
  have h := etaleOrdinaryConstantRestrictionPullback a f (ModuleCat.of D D)
  erw [ordinaryConstant_unit D f] at h
  exact h

private theorem exactSingleCoefficient_hom
    {A B E H : Type*} [Category A] [Category B] [Category E] [Category H]
    [Abelian A] [Abelian B] [Abelian E] [Abelian H]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (U : E ⥤ A) (G : E ⥤ H) (V : H ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory A ⥤ DerivedCategory B) (ε : L ≅ F.mapDerivedCategory)
    (e : U ⋙ F ≅ G ⋙ V) {M : E} {N : H} (α : G.obj M ≅ N)
    (d : L.obj ((DerivedCategory.singleFunctor A 0).obj (U.obj M)) ⟶
      (DerivedCategory.singleFunctor B 0).obj (F.obj (U.obj M)))
    (hd : d = ε.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M)) :
    (exactSingleCoefficientIso F U G V L ε e α).hom =
      d ≫ (DerivedCategory.singleFunctor B 0).map (e.hom.app M ≫ V.map α.hom) := by
  rw [hd]
  exact (Category.assoc _ _ _).symm

private theorem singleComparison_hom
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)) :
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app W =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} C) f).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj W) ≫
      ((upperStar (ModuleCat.{u + 1} C) f).mapDerivedCategorySingleFunctor 0).hom.app W := by
  rfl

private theorem scalarCoefficientPullback_hom
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarCoefficientPullbackIso a f).hom =
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app
        (scalarCoefficientSheaf a Y) ≫
        (DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).map
          ((upperStarRestrictScalarsIsoSheaf a f).hom.app
              (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} D))) ≫
            (Sheaf.restrictScalars X.smallEtaleTopology a).map
              (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} D) f)).inv) := by
  exact exactSingleCoefficient_hom
    (upperStar (ModuleCat.{u + 1} C) f)
    (Sheaf.restrictScalars Y.smallEtaleTopology a)
    (upperStar (ModuleCat.{u + 1} D) f)
    (Sheaf.restrictScalars X.smallEtaleTopology a)
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} C) f)
    (upperStarRestrictScalarsIsoSheaf a f)
    (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} D) f)).symm
    ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} C) f).hom.app
      (scalarCoefficientSheaf a Y))
    (singleComparison_hom C f (scalarCoefficientSheaf a Y))

private theorem scalar_single_pasting
    {E : Type*} [Category E] {A B C D F G H I J : E}
    {l : A ⟶ B} {m : B ⟶ C} {q : C ⟶ D} {x : D ⟶ F} (xi : F ⟶ D)
    (hx : x ≫ xi = 𝟙 D) {δB : B ⟶ G} {n : G ⟶ F}
    {δA : A ⟶ H} {v : H ⟶ G} {e₁ : H ⟶ I} {e₂ : I ⟶ J}
    {r : J ⟶ F} {d : A ⟶ J}
    (hq : m ≫ q ≫ x = δB ≫ n) (hn : l ≫ δB = δA ≫ v)
    (hu : v ≫ n = e₁ ≫ e₂ ≫ r) (hd : d = δA ≫ e₁ ≫ e₂) :
    l ≫ m ≫ q = d ≫ r ≫ xi := by
  have h : (l ≫ m ≫ q) ≫ x = d ≫ r := by
    simp only [Category.assoc]
    rw [hq, ← Category.assoc, hn, Category.assoc, hu, hd]
    simp only [Category.assoc]
  simpa only [Category.assoc, hx, Category.comp_id] using
    congrArg (fun k ↦ k ≫ xi) h

/-- The degree-zero scalar coefficient identification commutes with inverse image.
Source: Stacks Tags 03EK and 07A6; Zheng Construction 2.26
(blueprint: lem-pur-etale-scalar-constant-pullback).

Proof: the sectionwise scalar restriction comparison has identity direct-image
mate. Transpose the ordinary square under inverse image and then under constant
sheaf/global sections. Naturality of evaluation and the units of constant sheaf
restriction give equality. At the unit over B the ordinary constant pullback is
the monoidal unit comparison. Exact derivation on single complexes and naturality
of its single comparisons now give the displayed square. -/
theorem etaleScalarConstantPullback
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
      ((ModuleCat.restrictScalars.{u + 1} a).obj (ModuleCat.of D D))
    let b (W : Scheme.{u}) :=
      (DerivedCategory.singleFunctor _ 0).mapIso
          ((constantCommuteCompose W.smallEtaleTopology
            (ModuleCat.restrictScalars.{u + 1} a)).app (ModuleCat.of D D)) ≪≫
        (Functor.mapDerivedCategorySingleFunctor
          (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
            ((ModuleCat.restrictScalars.{u + 1} a).obj (ModuleCat.of D D))
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.map (b Y).hom ≫
        (exceptionalConstantPullbackIso C f).hom.app V =
      (scalarCoefficientPullbackIso a f).hom ≫ (b X).hom := by
  intro V b
  dsimp only [V, b, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} C) f).hom.naturality (coefficientConstantMap a Y)
  dsimp only [Functor.comp_map] at hn
  have hu := congrArg
    ((DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).map)
    (coefficientConstantMap_pullback a f)
  simp only [Functor.map_comp] at hu
  have hd := scalarCoefficientPullback_hom a f
  simp only [Functor.map_comp] at hd
  refine scalar_single_pasting
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)
      ).mapDerivedCategorySingleFunctor 0).inv.app
        ((ModuleCat.restrictScalars.{u + 1} a).obj (ModuleCat.of D D)))
    (Iso.hom_inv_id_app _ ((ModuleCat.restrictScalars.{u + 1} a).obj (ModuleCat.of D D)))
    ?_ hn hu hd
  -- `exact` here makes the kernel unfold the derived single comparisons (about 4 GB).
  transport_exact etaleConstantPullback_single C f
    ((ModuleCat.restrictScalars.{u + 1} a).obj (ModuleCat.of D D))

end AlgebraicGeometry.Etale
