/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Ordinary scalar tensor coordinates and total pullback

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-tensor-ordinary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

/-- The restricted universal scalar counit on cochain representatives.
Source: Stacks 06YY (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorScalarCounit {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules W A) ℤ) :
    (restriction a).mapDerivedCategory.obj
        ((proEtaleRingDerivedExtension a).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj
        (((restriction a).mapHomologicalComplex (.up ℤ)).obj
          (((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P)) :=
  cast (by rfl) ((restriction a).mapDerivedCategory.map
      ((proEtaleRingDerivedExtensionCounit a).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (restriction a).mapDerivedCategoryFactorsh.hom.app
      (((proEtaleRingExtension a).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))

/-- The one-sided tensor comparison in the specified scalar coordinates.
Source: Stacks 06YY (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorScalarCoordinates {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel W A) (P : CochainComplex (proEtaleRingModules W A) ℤ) :
    t.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (coefficientComplex a)) ⟶
      DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor P (coefficientComplex a) (proEtaleOrdinaryTensor W A)) :=
  (derivedTensorIso a t).inv.app (DerivedCategory.Q.obj P) ≫
    tensorScalarCounit a P ≫ DerivedCategory.Q.map (ordinaryComplexIso a P).hom

/-- The coefficient identification before localization, including the single-complex map.
Source: Stacks 03EL (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorCoefficientComplexPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :
    (((proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj (coefficientComplex a)) ≅
      coefficientComplex (inverseMap f a) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _))
    (.up ℤ) 0).app (coefficient a)) ≪≫
    (CochainComplex.singleFunctor (proEtaleRingModules Z (inverseRing f A))
      (0 : ℤ)).mapIso (coefficientPullback f a)

/-- Ordinary total tensor pullback, followed by the fixed coefficient identification.
Source: Stacks 03EL, 07A4 (blueprint: lem-sfb-scalar-tensor-ordinary-pullback). -/
@[irreducible] def tensorScalarOrdinaryPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules T A) ℤ) :
    (((proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P (coefficientComplex a) (proEtaleOrdinaryTensor T A))) ⟶
      CochainComplex.mapBifunctor
        (((proEtaleRingModulePullback f A (inverseRing f A)
          (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P)
        (coefficientComplex (inverseMap f a)) (proEtaleOrdinaryTensor Z (inverseRing f A)) :=
  (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _)
    P (coefficientComplex a)).inv ≫
    HomologicalComplex.mapBifunctorMap (𝟙 _)
      (tensorCoefficientComplexPullback f a).hom
      (proEtaleOrdinaryTensor Z (inverseRing f A)) (.up ℤ)

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  proEtaleRingModulePullback proEtaleRingDerivedPullbackFactors
  SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso HomologicalComplex₂.total
  Functor.mapBifunctorHomologicalComplex
attribute [local implicit_reducible] Functor.map₂HomologicalComplex

private theorem uncurry_map_id_left {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D ⥤ E)
    (X : C) {Y Y' : D} (v : Y ⟶ Y') :
    (Functor.uncurry.obj F).map (Prod.mkHom (𝟙 X) v) = (F.obj X).map v := by
  change (F.map (𝟙 X)).app Y ≫ (F.obj X).map v = _
  rw [F.map_id, NatTrans.id_app, Category.id_comp]

/-- Naturality of ordinary total pullback with the fixed coefficient augmentation.
Source: Stacks 07A4 (blueprint: lem-sfb-scalar-tensor-ordinary-pullback).
Proof: use naturality of the total comparison from the tensor descent data at
(1,q), then compose its second factor with the coefficient complex comparison.
Functoriality of the total bifunctor identifies that composite with (1,Fq ≫ k).
The degree-zero coefficient introduces no additional interchange sign. -/
theorem tensorScalarOrdinaryPullback_naturality
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P Q : CochainComplex (proEtaleRingModules T A) ℤ)
    (q : Q ⟶ coefficientComplex a) :
    let F := (proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)
    let TT := Functor.uncurry.obj ((proEtaleOrdinaryTensor T A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
    let TZ := Functor.uncurry.obj ((proEtaleOrdinaryTensor Z (inverseRing f A)
      ).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
    F.map (TT.map (Prod.mkHom (𝟙 P) q)) ≫ tensorScalarOrdinaryPullback f a P =
      (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _) P Q).inv ≫
        TZ.map (Prod.mkHom (𝟙 (F.obj P))
          (F.map q ≫ (tensorCoefficientComplexPullback f a).hom)) := by
  dsimp only
  let F := (proEtaleRingModulePullback f A (inverseRing f A)
    (Iso.refl _)).mapHomologicalComplex (.up ℤ)
  let TT := Functor.uncurry.obj ((proEtaleOrdinaryTensor T A).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let TZ := Functor.uncurry.obj ((proEtaleOrdinaryTensor Z (inverseRing f A)
    ).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  let C := coefficientComplex a
  let k := tensorCoefficientComplexPullback f a
  obtain ⟨_, _, e, he⟩ := proEtaleTensorPullbackDescentData f A (inverseRing f A) (Iso.refl _)
  have hn := e.inv.naturality (Prod.mkHom (𝟙 P) q)
  rw [he, he] at hn
  change F.map (TT.map (Prod.mkHom (𝟙 P) q)) ≫
      (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _)
        P C).inv =
    (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _)
      P Q).inv ≫ TZ.map (Prod.mkHom (F.map (𝟙 P)) (F.map q)) at hn
  unfold tensorScalarOrdinaryPullback
  have hcoef : HomologicalComplex.mapBifunctorMap (𝟙 (F.obj P)) k.hom
      (proEtaleOrdinaryTensor Z (inverseRing f A)) (.up ℤ) =
      TZ.map (Prod.mkHom (𝟙 (F.obj P)) k.hom) :=
    (uncurry_map_id_left ((proEtaleOrdinaryTensor Z (inverseRing f A)
      ).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) (F.obj P) k.hom).symm
  erw [hcoef, ← Category.assoc, hn, Category.assoc, ← TZ.map_comp]
  congr 2
  apply Prod.ext
  · change F.map (𝟙 P) ≫ 𝟙 (F.obj P) = 𝟙 (F.obj P)
    rw [F.map_id, Category.id_comp]
  · rfl

end AlgebraicGeometry.Scheme.DerivedScalarMate
