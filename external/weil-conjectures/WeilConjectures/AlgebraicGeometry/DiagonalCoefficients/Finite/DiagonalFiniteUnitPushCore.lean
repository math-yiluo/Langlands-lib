/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteRealization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteConstantAdjunct
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteUnitTransport

import WeilConjectures.CategoryTheory.SixFunctors.CompIsoApp

/-! # Normalized finite coefficient-unit square

Source: diagonal tower coefficient changes (1), normalized finite push square.
(blueprint: lem-diagonal-finite-unit-push)
-/

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
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint FiniteRealization.derivedUnit Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnitQ finiteConstantAbComparison finiteUnitComparison
  HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem canonical_single_comparison
    {C B : Type a} [Category.{v} C] [Category.{v} B]
    [Abelian C] [Abelian B] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ B) [F.Additive]
    (D : DiagonalRightDerived F) (e : D.R = F.rightDerivedFunctor)
    (h : IsCanonicalRightDerived F D e) (M : C) :
    singlePushComparison D M ≫
        (eqToIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        F.rightDerivedFunctorUnitQ ((HomologicalComplex.single C (.up ℤ) 0).obj M) := by
  unfold singlePushComparison
  rw [Category.assoc]
  exact congrArg (fun k ↦ DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫ k)
      (h ((HomologicalComplex.single C (.up ℤ) 0).obj M))

private theorem realized_unit_one
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] (Y : Scheme.{u})
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (D : DiagonalRightDerived (CondensedRing.lowerStar R (ProjectiveLine Y ↘ Y)))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (s : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY D D') :
    let m := eY.unitIso.inv ≫ eY.F.map (coefficientOrdinaryUnit R Y) ≫
      s.ordinary.hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).map eP.unitIso.hom
    (@MonObj.one _ _ _ (finiteConstantAbRing A Y)
        ((sfbConstantRing Y).obj (RingCat.of A)).mon) ≫ (finiteConstantAbComparison A Y).inv ≫
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map m ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (finiteConstantAbComparison A (ProjectiveLine Y)).hom =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)) ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (@MonObj.one _ _ _ (finiteConstantAbRing A (ProjectiveLine Y))
        ((sfbConstantRing (ProjectiveLine Y)).obj (RingCat.of A)).mon) := by
  let UY := Mod.regular (condensedRingObj R Y)
  let UP := Mod.regular (condensedRingObj R (ProjectiveLine Y))
  let FY := sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let FP := sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let G := lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)
  let m := coefficientOrdinaryUnit R Y
  let CY := (sfbConstantRing Y).obj (RingCat.of A)
  let CP := (sfbConstantRing (ProjectiveLine Y)).obj (RingCat.of A)
  let cY : FY.obj (geoCartierConstant A Y) ≅ CY.X := finiteConstantAbComparison A Y
  let cP : FP.obj (geoCartierConstant A (ProjectiveLine Y)) ≅ CP.X :=
    finiteConstantAbComparison A (ProjectiveLine Y)
  have hYn := eY.unit_normalization
  change eY.underlying.inv.app UY ≫ FY.map eY.unitIso.hom ≫ cY.hom =
    eY.coefficient.hom.hom at hYn
  have hPn := eP.unit_normalization
  change eP.underlying.inv.app UP ≫ FP.map eP.unitIso.hom ≫ cP.hom =
    eP.coefficient.hom.hom at hPn
  have hY : η[CY.X] ≫ cY.inv ≫ FY.map eY.unitIso.inv =
    η[condensedRingObj R Y] ≫ eY.underlying.inv.app UY := by
    apply (cancel_mono (FY.map eY.unitIso.hom ≫ cY.hom)).mp
    simp only [Category.assoc, ← FY.map_comp_assoc, Iso.inv_hom_id,
      FY.map_id, Category.id_comp]
    rw [hYn]
    exact (IsMonHom.one_hom (f := eY.coefficient.hom.hom)).symm
  have hP : η[condensedRingObj R (ProjectiveLine Y)] ≫
      eP.underlying.inv.app UP ≫ FP.map eP.unitIso.hom ≫ cP.hom = η[CP.X] := by
    rw [hPn]
    exact IsMonHom.one_hom (f := eP.coefficient.hom.hom)
  have ho := eq_of_heq (s.ordinary_normalization UP)
  have ht : eY.underlying.inv.app
      ((CondensedRing.lowerStar R (ProjectiveLine Y ↘ Y)).obj UP) ≫
      FY.map (s.ordinary.hom.app UP) = G.map (eP.underlying.inv.app UP) := by
    apply (cancel_mono (G.mapIso (eP.underlying.app UP)).hom).mp
    change eY.underlying.inv.app _ ≫ FY.map (s.ordinary.hom.app UP) ≫
      G.map (eP.underlying.hom.app UP) =
      G.map (eP.underlying.inv.app UP) ≫ G.map (eP.underlying.hom.app UP)
    erw [← G.map_comp, Iso.inv_hom_id_app, G.map_id, ho, Iso.inv_hom_id_app]
    rfl
  have hn := eY.underlying.inv.naturality m
  change m.hom ≫ eY.underlying.inv.app
      ((CondensedRing.lowerStar R (ProjectiveLine Y ↘ Y)).obj UP) =
    eY.underlying.inv.app UY ≫ FY.map (eY.F.map m) at hn
  change η[CY.X] ≫ cY.inv ≫ FY.map
      (eY.unitIso.inv ≫ eY.F.map m ≫ s.ordinary.hom.app UP ≫
        (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).map eP.unitIso.hom) ≫
      G.map cP.hom = Functor.LaxMonoidal.ε G ≫ G.map η[CP.X]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hY, ← reassoc_of% hn, reassoc_of% ht]
  rw [coefficientOrdinaryUnit_underlying]
  have hc : η[condensedRingObj R Y] ≫
      condensedPushforwardHom R (ProjectiveLine Y ↘ Y) =
    Functor.LaxMonoidal.ε G ≫ G.map η[condensedRingObj R (ProjectiveLine Y)] :=
    (isMonHom_condensedPushforwardHom R (ProjectiveLine Y ↘ Y)).one_hom
  erw [reassoc_of% hc]
  change Functor.LaxMonoidal.ε G ≫ G.map η[condensedRingObj R (ProjectiveLine Y)] ≫
      G.map (eP.underlying.inv.app UP) ≫ G.map (FP.map eP.unitIso.hom) ≫
        G.map cP.hom = _
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ Functor.LaxMonoidal.ε G ≫ G.map k) hP

private theorem native_adjunct_in_model
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (m : geoCartierConstant A Y ⟶
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (h : (@MonObj.one _ _ _ (finiteConstantAbRing A Y)
        ((sfbConstantRing Y).obj (RingCat.of A)).mon) ≫ (finiteConstantAbComparison A Y).inv ≫
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map m ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (finiteConstantAbComparison A (ProjectiveLine Y)).hom =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)) ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (@MonObj.one _ _ _ (finiteConstantAbRing A (ProjectiveLine Y))
        ((sfbConstantRing (ProjectiveLine Y)).obj (RingCat.of A)).mon))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (hc : D'.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y))
    (hcanonical : IsCanonicalRightDerived
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) D' hc) :
    (DerivedCategory.singleFunctor _ 0).map m ≫
      singlePushComparison D' (geoCartierConstant A (ProjectiveLine Y)) ≫
      (eqToIso hc).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (geoCartierConstant A (ProjectiveLine Y))) ≫
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map
        (finiteUnitComparison A (ProjectiveLine Y)).inv =
      (finiteUnitComparison A Y).inv ≫ finiteUnitAdjunct A Y := by
  have hm := finite_constant_adjunct_of_one A Y m h
  have hcan := canonical_single_comparison
    (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) D' hc hcanonical
    (geoCartierConstant A (ProjectiveLine Y))
  calc
    _ = (DerivedCategory.singleFunctor _ 0).map m ≫
        (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) (.up ℤ) 0).inv.app
              (geoCartierConstant A (ProjectiveLine Y))) ≫
          (lowerStar (ModuleCat.{u + 1} A)
            (ProjectiveLine Y ↘ Y)).rightDerivedFunctorUnitQ
              ((HomologicalComplex.single _ (.up ℤ) 0).obj
                (geoCartierConstant A (ProjectiveLine Y)))) ≫
        (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map
          (finiteUnitComparison A (ProjectiveLine Y)).inv := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (DerivedCategory.singleFunctor _ 0).map m ≫ k ≫
          (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map
            (finiteUnitComparison A (ProjectiveLine Y)).inv) hcan
    _ = _ := by simpa only [Category.assoc] using hm

attribute [local irreducible] DerivedCategory.singleFunctors

private theorem finite_unit_identity
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X) :
    let i : e.F.mapDerivedCategory.obj (unit R X) ≅ geoP1Unit A X :=
      (e.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e.unitIso ≪≫
          (finiteUnitComparison A X).symm
    i.inv ≫ e.F.mapDerivedCategory.map (𝟙 (unit R X)) ≫ e.derivedUnit =
      𝟙 (geoP1Unit A X) := by
  let i : e.F.mapDerivedCategory.obj (unit R X) ≅ geoP1Unit A X :=
    (e.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e.unitIso ≪≫
        (finiteUnitComparison A X).symm
  have hi : i.hom = e.derivedUnit := by
    unfold i FiniteRealization.derivedUnit
    try unfold Functor.compIsoApp
    rfl
  change i.inv ≫ e.F.mapDerivedCategory.map (𝟙 (unit R X)) ≫ e.derivedUnit = 𝟙 _
  rw [e.F.mapDerivedCategory.map_id, Category.id_comp, ← hi]
  exact i.inv_hom_id

/-- The normalized finite push square on the coefficient unit, before cancellation
of the finite realization unit isomorphism. This is the single-object instance of
`FinitePushSquare.derived.normalization`, combined with the ordinary unit
normalization and the canonical derived-unit equation. The ordinary square is
first evaluated on the regular module, then the single-complex comparisons are
cancelled; the result is the displayed equation. No line, trace, or positivity
hypothesis enters this coefficient-unit step.
(blueprint: lem-diagonal-finite-unit-push-square)

Proof: evaluate the supplied finite push-square normalization at the regular module,
use the ordinary unit normalization to identify the coefficient map, cancel the
single-complex comparison isomorphisms, and apply the canonical derived-unit
equation and the finite adjunction hom-equivalence. -/
theorem finite_unit_push_square
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] (Y : Scheme.{u})
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (D : DiagonalRightDerived (CondensedRing.lowerStar R (ProjectiveLine Y ↘ Y)))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (hc : D'.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y))
    (hcanonical : IsCanonicalRightDerived
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) D' hc)
    (s : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY D D') :
    let t := s.derived.iso.hom ≫
      Functor.whiskerLeft eP.F.mapDerivedCategory (eqToIso hc).hom
    let i : eP.F.mapDerivedCategory.obj (unit R (ProjectiveLine Y)) ≅
        geoP1Unit A (ProjectiveLine Y) :=
      (eP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso eP.unitIso ≪≫
          (finiteUnitComparison A (ProjectiveLine Y)).symm
    eY.F.mapDerivedCategory.map (coefficientUnitPush R Y D) ≫
        t.app (unit R (ProjectiveLine Y)) ≫
        (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map eP.derivedUnit =
      eY.derivedUnit ≫ finiteUnitAdjunct A Y ≫
        (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map
          (i.inv ≫
            eP.F.mapDerivedCategory.map (𝟙 (unit R (ProjectiveLine Y))) ≫
              eP.derivedUnit) := by
  let m := eY.unitIso.inv ≫ eY.F.map (coefficientOrdinaryUnit R Y) ≫
    s.ordinary.hom.app (Mod.regular (condensedRingObj R (ProjectiveLine Y))) ≫
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).map eP.unitIso.hom
  have hm : eY.F.map (coefficientOrdinaryUnit R Y) ≫
      s.ordinary.hom.app (Mod.regular (condensedRingObj R (ProjectiveLine Y))) ≫
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).map eP.unitIso.hom =
      eY.unitIso.hom ≫ m := by
    simp only [m, Iso.hom_inv_id_assoc]
  have hOne := realized_unit_one Y eY eP D D' s
  have hn := native_adjunct_in_model A Y m hOne D' hc hcanonical
  have hid := finite_unit_identity eP
  dsimp only
  rw [hid, (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map_id, Category.comp_id]
  unfold coefficientUnitPush
  exact finite_push_unit_transport R A (ProjectiveLine Y ↘ Y) eP eY D D' hc s
    (coefficientOrdinaryUnit R Y) (finiteUnitAdjunct A Y) m hm hn

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

end
