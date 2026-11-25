/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Logic.Small.Defs

import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Logic.Small.Defs

/-!
# Specified scalar/pullback representative data

These are the existing comparison constructions, shared by the representative
computation and the theorem identifying its geometric mate with projection.

## References

* Stacks Project, Tags 07A4, 07A6 and 07A7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

/-- The ordinary scalar/pullback identification, conjugate to the sectionwise
restriction/direct-image identity under the two composite adjunctions. -/
def scalarSheafPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    ProEtale.etaleSheafExtendScalars φ W ⋙ upperStar (ModuleCat.{u + 1} B) f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ProEtale.etaleSheafExtendScalars φ Z :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ Z))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
    (lowerStarCompRestrictScalarsIso φ f).symm

/-- The same comparison on actual cochain complexes. -/
def scalarSheafPullbackComplexIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :=
  Functor.mapHomologicalComplexCompIso (scalarSheafPullbackIso φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (upperStar (ModuleCat.{u + 1} A) f ⋙
        ProEtale.etaleSheafExtendScalars φ Z)) (.up ℤ)).symm

private theorem representative_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D) (e : L ≅ F.mapDerivedCategory)
    (τ : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hτ : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ F.mapDerivedCategoryFactorsh.hom = τ)
    (P : CochainComplex C ℤ) :
    τ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P := by
  rw [← hτ]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryFactorsh_hom_app]
  have hq (P : CochainComplex (C) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app P = 𝟙 _ := rfl
  have hq' (P : CochainComplex (D) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app P = 𝟙 _ := rfl
  rw [hq, hq']
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The geometric derived counit, with the homotopy quotient comparison included. -/
def scalarGeometricRepresentative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) :=
  L(upperStar (ModuleCat.{u + 1} A) f).map
      ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Qh.map
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P)

/-- The exact geometric representative through the canonical derived comparison. -/
private theorem scalarGeometricRepresentative_eq
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    scalarGeometricRepresentative A f P =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        (DerivedCategory.Q.obj P) ≫
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom.app P := by
  have h := representative_eq (upperStar (ModuleCat.{u + 1} A) f)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac P
  have hq : (DerivedCategory.quotientCompQhIso _).inv.app P = 𝟙 _ := rfl
  have hq' : (DerivedCategory.quotientCompQhIso _).hom.app
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  dsimp only [scalarGeometricRepresentative]
  rw [hq, hq']
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact h

private theorem scalarGeometricRepresentative_exact
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    scalarGeometricRepresentative A f P =
      Functor.exactDerivedRepresentative (upperStar (ModuleCat.{u + 1} A) f)
        L(upperStar (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) P := by
  exact scalarGeometricRepresentative_eq A f P

end AlgebraicGeometry.Etale
private theorem complex_square_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P =
      ((Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).symm).hom.app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.comp_obj]
  exact (Category.comp_id _).symm

namespace CategoryTheory.Functor
private theorem square_cochain_fac {A B B' E : Type*} [Category A] [Category B] [Category B']
  [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : CochainComplex A ℤ) :
    F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj X) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app X) ≫
        (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app X) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj X) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app X) := by
  have hF := mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ X
  have hG := mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ X
  have he := mapDerivedCategoryNatIso_fac e X
  have hF' : F₂.mapDerivedCategoryFactors.inv.app
        ((F₁.mapHomologicalComplex (.up ℤ)).obj X) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app X) ≫
      (mapDerivedCategoryCompIso F₁ F₂).hom.app (DerivedCategory.Q.obj X) =
        (F₁ ⋙ F₂).mapDerivedCategoryFactors.inv.app X := by
    apply (cancel_mono ((F₁ ⋙ F₂).mapDerivedCategoryFactors.hom.app X)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [← hF, Iso.hom_inv_id_app_assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rfl
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hF', hG, he, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
section ExactRepresentativeAPI
attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctorCounit Functor.rightDerivedFunctorUnit
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.mapDerivedCategoryNatIso

private theorem exactSquareRepresentative
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F₁ : B ⥤ A) (F₂ : A ⥤ E) (G₁ : B ⥤ D) (G₂ : D ⥤ E)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (L : DerivedCategory A ⥤ DerivedCategory E)
    (M : DerivedCategory B ⥤ DerivedCategory D)
    (ε : L ≅ F₂.mapDerivedCategory) (δ : M ≅ G₁.mapDerivedCategory)
    (P : CochainComplex B ℤ) :
    L.map
        (F₁.mapDerivedCategoryFactors.inv.app P) ≫
      (Functor.exactDerivedComparisonSquare F₁ F₂ G₁ G₂ e L M ε δ).hom.app
          (_root_.DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map
        (Functor.exactDerivedRepresentative G₁ M δ P) ≫
      G₂.mapDerivedCategoryFactors.hom.app
        ((G₁.mapHomologicalComplex (.up ℤ)).obj P) =
    (Functor.exactDerivedRepresentative F₂ L ε ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      _root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).symm).hom.app P) := by
  simp only [Functor.exactDerivedComparisonSquare, Functor.exactDerivedRepresentative,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  erw [ε.hom.naturality_assoc]
  have h :
      F₂.mapDerivedCategoryFactors.inv.app
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        F₂.mapDerivedCategory.map
          (F₁.mapDerivedCategoryFactors.inv.app P) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app
          (_root_.DerivedCategory.Q.obj P) ≫
        G₂.mapDerivedCategory.map
          (G₁.mapDerivedCategoryFactors.hom.app P) ≫
        G₂.mapDerivedCategoryFactors.hom.app
          ((G₁.mapHomologicalComplex (.up ℤ)).obj P) =
      _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          e.hom (.up ℤ)).app P) :=
    CategoryTheory.Functor.square_cochain_fac e P
  have hh := congrArg
    (fun z ↦ F₂.mapDerivedCategoryFactors.hom.app
      ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫ z) h
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc] at hh
  rw [hh]
  apply congrArg (fun z ↦
    ε.hom.app
      (DerivedCategory.Q.obj
        ((F₁.mapHomologicalComplex
          (.up ℤ)).obj P)) ≫
    F₂.mapDerivedCategoryFactors.hom.app
      ((F₁.mapHomologicalComplex
        (.up ℤ)).obj P) ≫ z)
  rw [← DerivedCategory.Q.map_comp]
  apply congrArg DerivedCategory.Q.map
  exact complex_square_hom e P

private theorem exactSquareRepresentativeOfEq
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F₁ : B ⥤ A) (F₂ : A ⥤ E) (G₁ : B ⥤ D) (G₂ : D ⥤ E)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (L : DerivedCategory A ⥤ DerivedCategory E)
    (M : DerivedCategory B ⥤ DerivedCategory D)
    (ε : L ≅ F₂.mapDerivedCategory) (δ : M ≅ G₁.mapDerivedCategory)
    (γ : ∀ P : CochainComplex A ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F₂.mapHomologicalComplex (.up ℤ)).obj P))
    (ζ : ∀ P : CochainComplex B ℤ, M.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G₁.mapHomologicalComplex (.up ℤ)).obj P))
    (hγ : ∀ P, γ P = Functor.exactDerivedRepresentative F₂ L ε P)
    (hζ : ∀ P, ζ P = Functor.exactDerivedRepresentative G₁ M δ P)
    (χ : F₁.mapDerivedCategory ⋙ L ≅ M ⋙ G₂.mapDerivedCategory)
    (hχ : χ = Functor.exactDerivedComparisonSquare F₁ F₂ G₁ G₂ e L M ε δ)
    (P : CochainComplex B ℤ) :
    L.map
        (F₁.mapDerivedCategoryFactors.inv.app P) ≫
      χ.hom.app
          (_root_.DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map (ζ P) =
    (γ ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      _root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).symm).hom.app P) ≫
      G₂.mapDerivedCategoryFactors.inv.app
        ((G₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply (cancel_mono (G₂.mapDerivedCategoryFactors.hom.app
    ((G₁.mapHomologicalComplex (.up ℤ)).obj P))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hχ, hγ, hζ]
  erw [Category.comp_id]
  exact exactSquareRepresentative F₁ F₂ G₁ G₂ e L M ε δ P

section RepresentativeEquations

private theorem scalarRestrictionPullbackIso_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
    type_of% (exactSquareRepresentativeOfEq
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} B) f)
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (upperStarRestrictScalarsIsoSheaf φ f)
    L(upperStar (ModuleCat.{u + 1} A) f) L(upperStar (ModuleCat.{u + 1} B) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    (scalarGeometricRepresentative A f) (scalarGeometricRepresentative B f)
    (scalarGeometricRepresentative_exact A f) (scalarGeometricRepresentative_exact B f)
    (scalarRestrictionPullbackIso φ f) rfl P) :=
  exactSquareRepresentativeOfEq
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} B) f)
    (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (upperStarRestrictScalarsIsoSheaf φ f)
    L(upperStar (ModuleCat.{u + 1} A) f) L(upperStar (ModuleCat.{u + 1} B) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    (scalarGeometricRepresentative A f) (scalarGeometricRepresentative B f)
    (scalarGeometricRepresentative_exact A f) (scalarGeometricRepresentative_exact B f)
    (scalarRestrictionPullbackIso φ f) rfl P

private theorem scalarGeometricRepresentative_naturality
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X)
    {P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (g : P ⟶ Q) :
    L(upperStar (ModuleCat.{u + 1} A) f).map (_root_.DerivedCategory.Q.map g) ≫
      scalarGeometricRepresentative A f Q =
    scalarGeometricRepresentative A f P ≫ _root_.DerivedCategory.Q.map
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map g) := by
  simp only [scalarGeometricRepresentative_eq, Category.assoc]
  have h := (Functor.whiskerLeft _root_.DerivedCategory.Q
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom ≫
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom).naturality g
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map,
    Category.assoc] using h

end RepresentativeEquations
end ExactRepresentativeAPI

/-- The single-complex comparison for an exact pullback and a coefficient square. -/
def exactSingleCoefficientIso
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (U : E ⥤ C) (G : E ⥤ H) (V : H ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D) (ε : L ≅ F.mapDerivedCategory)
    (e : U ⋙ F ≅ G ⋙ V) {M : E} {N : H} (α : G.obj M ≅ N) :
    L.obj ((DerivedCategory.singleFunctor C 0).obj (U.obj M)) ≅
      (DerivedCategory.singleFunctor D 0).obj (V.obj N) :=
  ε.app _ ≪≫ (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor D 0).mapIso (e.app M ≪≫ V.mapIso α)

/-- The specified identification f_A^{-1}B_W[0] = B_Z[0]. -/
def scalarCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (scalarCoefficient φ W) ≅
      scalarCoefficient φ Z :=
  exactSingleCoefficientIso
    (upperStar (ModuleCat.{u + 1} A) f)
    (Sheaf.restrictScalars W.smallEtaleTopology φ)
    (upperStar (ModuleCat.{u + 1} B) f)
    (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (upperStarRestrictScalarsIsoSheaf φ f)
    (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) f)).symm

end AlgebraicGeometry.Etale
