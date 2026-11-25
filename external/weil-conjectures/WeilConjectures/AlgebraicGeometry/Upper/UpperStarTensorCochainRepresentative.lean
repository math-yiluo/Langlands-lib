/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs

import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-!
# The tensor counit square on cochain representatives

Source: Stacks Project, Tags 07A4 and 0FPH
(blueprint: lem-pur-upper-star-tensor-cochain-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar
  Functor.leftDerivedFunctorCounit Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh

private theorem quotient_map_Qh
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P R : CochainComplex C ℤ} (a : P ⟶ R) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map a) =
      DerivedCategory.Q.map a := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality a
  have hi (K : CochainComplex C ℤ) :
      (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  rw [hi, hi] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

private theorem quotient_tensorator
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (P R : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P R =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj R) := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫
      𝟙 _ = _
  simp only [tensorHom_id, CategoryTheory.Functor.map_id, id_whiskerRight,
    Category.id_comp, Category.comp_id]
  rfl

private theorem cochain_tensor_counit_core
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.Monoidal] [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ (DerivedCategory D)).obj L).obj L).obj
        (curriedTensor (DerivedCategory D)))
    (e : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (r : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
    (hδ : LaxSquareHδ (Q₁ := DerivedCategory.Qh) (Q₂ := DerivedCategory.Qh)
      (F := F.mapHomotopyCategory (.up ℤ)) δ (fun K ↦ e.app K))
    : LaxSquareHδ (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
      (F := F.mapHomologicalComplex (.up ℤ)) δ r := by
  intro P R
  simp only [hr, quotient_tensorator]
  have h := hδ ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj R)
  simp only [Functor.mapHomotopyCategory_δ,
    Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, quotient_map_Qh] at h
  exact h

private theorem representative_quotient
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (η : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    η.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) =
        η.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  have hi : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl
  rw [hi]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The defining derived tensor counit square on arbitrary cochain complexes.
Source: Stacks Project, Tags 07A4 and 0FPH
(blueprint: lem-pur-upper-star-tensor-cochain-representative).
Proof: apply the homotopy-category counit square to the quotients of P and R.
The quotient tensorator and mapHomotopyCategoryFactors have identity components;
quotientCompQhIso identifies Qh on quotient morphisms with Q. These identities
transport the square to exactly the displayed geometric representatives. -/
theorem upperStar_tensor_cochain_representative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    : LaxSquareHδ (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
      (F := (upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ))
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
      (scalarGeometricRepresentative A f) := by
  refine cochain_tensor_counit_core (upperStar (ModuleCat.{u + 1} A) f)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (scalarGeometricRepresentative A f) ?_
    (leftDerivedUpperStarTensorComparison_laxSquareHδ (ModuleCat.{u + 1} A) f)
  intro P
  have hq : (DerivedCategory.quotientCompQhIso _).inv.app P = 𝟙 _ := rfl
  have hq' : (DerivedCategory.quotientCompQhIso _).hom.app
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  dsimp only [scalarGeometricRepresentative]
  rw [hq, hq']
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact representative_quotient (upperStar (ModuleCat.{u + 1} A) f)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit P

end AlgebraicGeometry.Etale
