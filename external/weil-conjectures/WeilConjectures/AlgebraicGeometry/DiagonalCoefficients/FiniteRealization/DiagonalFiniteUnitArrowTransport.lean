/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteUnitPush

import WeilConjectures.CategoryTheory.SixFunctors.CompIsoApp

/-! # Finite realization of a unit followed by a local arrow

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
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
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint FiniteRealization.derivedUnit
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem transport_unit_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ C') (G : D ⥤ D') (R : D ⥤ C) (R' : D' ⥤ C')
    (t : R ⋙ F ⟶ G ⋙ R')
    {U : C} {V W : D} {U' : C'} {V' W' : D'}
    (a : U ⟶ R.obj V) (a' : U' ⟶ R'.obj V')
    (u : F.obj U ⟶ U') (i : G.obj V ≅ V') (z : V ⟶ W) (v : G.obj W ⟶ W')
    (h : F.map a ≫ t.app V ≫ R'.map i.hom = u ≫ a') :
    F.map (a ≫ R.map z) ≫ (t.app W ≫ R'.map v) =
      u ≫ (a' ≫ R'.map ((i.inv ≫ G.map z) ≫ v)) := by
  have hn := t.naturality z
  change F.map (R.map z) ≫ t.app W = t.app V ≫ R'.map (G.map z) at hn
  have hz : G.map z ≫ v = i.hom ≫ ((i.inv ≫ G.map z) ≫ v) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = F.map a ≫ t.app V ≫ R'.map (G.map z ≫ v) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hn]
    _ = (F.map a ≫ t.app V ≫ R'.map i.hom) ≫
        R'.map ((i.inv ≫ G.map z) ≫ v) := by
      rw [hz, R'.map_comp]
      simp only [Category.assoc]
    _ = _ := by rw [h]; simp only [Category.assoc]

/-- The specified finite realization unit isomorphism in the derived category.
Source: coefficient changes (1), the finite single-object unit comparison.
(blueprint: lem-diagonal-finite-unit-arrow-transport). -/
@[irreducible]
def FiniteRealization.unitIsoDerived
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X) :
    e.F.mapDerivedCategory.obj (unit R X) ≅ geoP1Unit A X :=
  (e.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e.unitIso ≪≫ (finiteUnitComparison A X).symm

/-- The hom of the finite derived unit is the prescribed unit arrow.
Source: coefficient changes (1), finite single-object unit comparison.
(blueprint: lem-diagonal-finite-unit-arrow-transport).
Proof: expand the composite isomorphism and the prescribed derived unit. -/
theorem FiniteRealization.unitIsoDerived_hom
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X) :
    e.unitIsoDerived.hom = e.derivedUnit := by
  unfold FiniteRealization.unitIsoDerived FiniteRealization.derivedUnit
  try unfold Functor.compIsoApp
  rfl

/-- Finite realization transports the coefficient-unit arrow followed by any local arrow.
Source: coefficient changes (1), finite unit normalization and adjunction naturality.
(blueprint: lem-diagonal-finite-unit-arrow-transport).
Proof: finite_unit_push gives the unit square. Naturality of its direct-image
comparison transports the local arrow. Insert and cancel the specified derived
unit isomorphism on P, then use finiteUnitAdjunct_naturality. -/
theorem finite_unit_arrow_transport
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] (Y : Scheme.{u})
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (D : DiagonalRightDerived (CondensedRing.lowerStar R (ProjectiveLine Y ↘ Y)))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (hc : D'.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y))
    (hcanonical : IsCanonicalRightDerived
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) D' hc)
    (s : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY D D')
    {W : DerivedCategory (Modules R (ProjectiveLine Y))}
    {W' : DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine Y))
      (ModuleCat.{u + 1} A))}
    (z : unit R (ProjectiveLine Y) ⟶ W) (v : eP.F.mapDerivedCategory.obj W ⟶ W') :
    let t := s.derived.iso.hom ≫
      Functor.whiskerLeft eP.F.mapDerivedCategory (eqToIso hc).hom
    eY.F.mapDerivedCategory.map (coefficientUnitPush R Y D ≫ D.R.map z) ≫
        (t.app W ≫ (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map v) =
      eY.derivedUnit ≫
        finiteAdjunct A Y ((eP.unitIsoDerived.inv ≫ eP.F.mapDerivedCategory.map z) ≫ v) := by
  let t := s.derived.iso.hom ≫
    Functor.whiskerLeft eP.F.mapDerivedCategory (eqToIso hc).hom
  have h := transport_unit_adjunct eY.F.mapDerivedCategory eP.F.mapDerivedCategory
    D.R (geoP1Pushforward A (ProjectiveLine Y ↘ Y)) t
    (coefficientUnitPush R Y D) (finiteUnitAdjunct A Y)
    eY.derivedUnit eP.unitIsoDerived z v
    (by
      rw [FiniteRealization.unitIsoDerived_hom]
      exact finite_unit_push Y eY eP D D' hc hcanonical s)
  exact h.trans (congrArg (fun w => eY.derivedUnit ≫ w)
    (finiteUnitAdjunct_naturality A Y _))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

end
