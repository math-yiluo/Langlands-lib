/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRealizedClassHom

/-! # Composition of supplied finite realization endpoints

Source: diagonal tower coefficient changes (1), scalar compatibility and Ext realization.
(blueprint: lem-diagonal-finite-realization-composition-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v u' v'
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

attribute [local irreducible] geoCartierConstant geoCartierLine
  quotientLine quotientLineMap cyclicLine cyclicLineMap
  derivedScalars QuotientLineRealization finiteRealizedClass CyclicCartierFrame.reduce
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor Endpoint.shift
  Mod.extendScalars AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  DerivedCategory.singleFunctorIsoCompQ
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Ext.homEquiv

private theorem realization_composition
    {C D K : Type*} [Category C] [Category D] [Category K]
    (F : C ⥤ D) (G : D ⥤ K) {S T : C} {X Z : D} {X' Z' : K}
    (a : F.obj S ≅ X) (b : G.obj X ≅ X') (u : F.obj T ⟶ Z)
    (v : G.obj Z ⟶ Z') (β : S ⟶ T) (α : X ⟶ Z)
    (h : F.map β ≫ u = a.hom ≫ α) :
    (G.mapIso a ≪≫ b).hom ≫ (b.inv ≫ G.map α ≫ v) =
      (F ⋙ G).map β ≫ (G.map u ≫ v) := by
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← G.map_comp_assoc, ← h, G.map_comp, Category.assoc]

/-- A compatible scalar square remains compatible after the supplied finite realization. -/
theorem finiteRealization_compositionCore
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
    {L : ∀ X : Scheme.{u}, Modules R X}
    (eW : FiniteRealization R A (diagonalSurface Y))
    (line : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
    (s : eW.F.obj (source R Y) ≅
      (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    {B : Type*} [Category B] (F : B ⥤ DerivedCategory (Modules R (diagonalSurface Y)))
    {S T : B}
    (a : F.obj S ≅ (DerivedCategory.singleFunctor _ 0).obj (source R Y))
    (t : F.obj T ⟶ ((DerivedCategory.singleFunctor _ 0).obj
      (L (diagonalSurface Y)))⟦(2 : ℤ)⟧)
    (β : S ⟶ T)
    (α : (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj
      (source R Y) ⟶ ((DerivedCategory.singleFunctor _ 0).obj
        (L (diagonalSurface Y)))⟦(2 : ℤ)⟧)
    (h : F.map β ≫ t = a.hom ≫ α) :
    (eW.F.mapDerivedCategory.mapIso a ≪≫
      (eW.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso s).hom ≫
        (finiteRealizedClass (L := L) N hA Y eW line s α).hom =
      (F ⋙ eW.F.mapDerivedCategory).map β ≫
        (eW.F.mapDerivedCategory.map t ≫
          (eW.F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
          ((eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
            (DerivedCategory.singleFunctor _ 0).map line.hom)⟦(2 : ℤ)⟧') := by
  conv_lhs =>
    arg 2
    rw [finiteRealizedClass_hom (L := L) N hA Y eW line s α]
  let D := DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0
  let e := eW.F.mapDerivedCategorySingleFunctor 0
  let b := e.app _ ≪≫ D.mapIso s
  let v := (eW.F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
    (e.hom.app _ ≫ D.map line.hom)⟦(2 : ℤ)⟧'
  have hh := realization_composition F eW.F.mapDerivedCategory a b t v β α h
  simpa only [SpTowerClasses.mapSingleArrow, b, v, e, D, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, Nat.cast_ofNat] using hh

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
