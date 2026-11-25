/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteRealization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush

import WeilConjectures.CategoryTheory.SixFunctors.CompIsoApp

/-! # Transport of a normalized native finite unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
section
universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint FiniteRealization.derivedUnit Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnitQ finiteConstantAbComparison finiteUnitComparison
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem finiteRealization_derivedUnit_eq
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X) :
    e.derivedUnit =
      (Functor.compIsoApp (e.F.mapDerivedCategorySingleFunctor 0)
          (Mod.regular (condensedRingObj R X))).hom ≫
        (DerivedCategory.singleFunctor _ 0).map e.unitIso.hom ≫
          (finiteUnitComparison A X).inv := by
  unfold FiniteRealization.derivedUnit
  rfl

private theorem transport_single_unit
    {A B C J : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} J]
    [Abelian A] [Abelian B] [Abelian C] [Abelian J]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} J]
    {F : A ⥤ B} {G : C ⥤ J} [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ J) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary)
    (H : DerivedCategory C ⥤ DerivedCategory J) (e : RG.R ≅ H)
    (M : A) (N : B) (v : N ⟶ F.obj M) (X : C) (Z : J)
    (iX : U.obj M ≅ X) (iZ : V.obj N ≅ Z)
    (S : DerivedCategory C) (T : DerivedCategory J)
    (cP : S ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (cY : T ≅ (DerivedCategory.singleFunctor J 0).obj Z) (b : T ⟶ H.obj S)
    (m : Z ⟶ G.obj X)
    (hm : V.map v ≫ ordinary.hom.app M ≫ G.map iX.hom = iZ.hom ≫ m)
    (hn : (DerivedCategory.singleFunctor J 0).map m ≫
      singlePushComparison RG X ≫
        e.hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫ H.map cP.inv =
      cY.inv ≫ b) :
    let t := s.iso.hom ≫ Functor.whiskerLeft U.mapDerivedCategory e.hom
    V.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor B 0).map v ≫ singlePushComparison RF M) ≫
      t.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        H.map ((Functor.compIsoApp (U.mapDerivedCategorySingleFunctor 0) M).hom ≫
          (DerivedCategory.singleFunctor C 0).map iX.hom ≫ cP.inv) =
    ((Functor.compIsoApp (V.mapDerivedCategorySingleFunctor 0) N).hom ≫
      (DerivedCategory.singleFunctor J 0).map iZ.hom ≫ cY.inv) ≫ b := by
  simp only [Functor.compIsoApp, Iso.app_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  let Q := DerivedCategory.singleFunctor J 0
  have hmap : Q.map (V.map v) ≫ Q.map (ordinary.hom.app M) ≫ Q.map (G.map iX.hom) =
      Q.map iZ.hom ≫ Q.map m := by
    simpa only [Q.map_comp, Category.assoc] using congrArg Q.map hm
  rw [← e.hom.naturality]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% singlePushComparison_square U V RF RG ordinary s M]
  erw [reassoc_of% (V.mapDerivedCategorySingleFunctor 0).hom.naturality v]
  erw [← reassoc_of% singlePushComparison_naturality RG iX.hom]
  erw [e.hom.naturality]
  calc
    _ = (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫ Q.map iZ.hom ≫
        (Q.map m ≫ singlePushComparison RG X ≫
          e.hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫ H.map cP.inv) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫ k ≫
          singlePushComparison RG X ≫
            e.hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫ H.map cP.inv) hmap
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫ Q.map iZ.hom ≫ k) hn

/-- A normalized native finite unit equation transports through a finite realization.
Source: diagonal tower coefficient changes (1), the normalized finite push square.
(blueprint: lem-diagonal-finite-unit-transport).

Proof: evaluate the full derived-square normalization on the single regular module.
Naturality of the exact single comparison moves the ordinary map through the source
realization. Naturality of singlePushComparison moves the target unit isomorphism
through the supplied right-derived model. Naturality of the model identification
then expresses the left side using the native map m. The ordinary factorization
hypothesis and the native derived-unit equation identify it with the source derived
unit followed by b. The generic private helper proves these operations before
specializing to scheme sheaves. No assumption on one, traces or line classes is
needed in this transport calculation. -/
theorem finite_push_unit_transport
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : FiniteRealization R A X) (eS : FiniteRealization R A S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) f))
    (hc : D'.R = geoP1Pushforward A f) (s : FinitePushSquare R A f eX eS D D')
    (a : Mod.regular (condensedRingObj R S) ⟶
      (CondensedRing.lowerStar R f).obj (Mod.regular (condensedRingObj R X)))
    (b : geoP1Unit A S ⟶ (geoP1Pushforward A f).obj (geoP1Unit A X))
    (m : geoCartierConstant A S ⟶
      (lowerStar (ModuleCat.{u + 1} A) f).obj (geoCartierConstant A X))
    (hm : eS.F.map a ≫ s.ordinary.hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} A) f).map eX.unitIso.hom = eS.unitIso.hom ≫ m)
    (hn : (DerivedCategory.singleFunctor _ 0).map m ≫
        singlePushComparison D' (geoCartierConstant A X) ≫
        (eqToIso hc).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (geoCartierConstant A X)) ≫
        (geoP1Pushforward A f).map (finiteUnitComparison A X).inv =
        (finiteUnitComparison A S).inv ≫ b) :
    let t := s.derived.iso.hom ≫
      Functor.whiskerLeft eX.F.mapDerivedCategory (eqToIso hc).hom
    eS.F.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (Modules R S) 0).map a ≫
          singlePushComparison D (Mod.regular (condensedRingObj R X))) ≫
        t.app (unit R X) ≫ (geoP1Pushforward A f).map eX.derivedUnit =
      eS.derivedUnit ≫ b := by
  rw [finiteRealization_derivedUnit_eq eX, finiteRealization_derivedUnit_eq eS]
  have h := transport_single_unit eX.F eS.F D D' s.ordinary s.derived
    (geoP1Pushforward A f) (eqToIso hc) (Mod.regular (condensedRingObj R X))
    (Mod.regular (condensedRingObj R S)) a (geoCartierConstant A X)
    (geoCartierConstant A S) eX.unitIso eS.unitIso
    (geoP1Unit A X) (geoP1Unit A S) (finiteUnitComparison A X) (finiteUnitComparison A S)
    b m hm hn
  simp only [Functor.compIsoApp, Iso.app_hom] at h ⊢
  exact h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

end
