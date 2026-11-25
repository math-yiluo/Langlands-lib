/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import all WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle

/-! The normalized coefficient unit in exact degree zero. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace SheafExactDegreeZero

private theorem derived_unit_epsilon
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C] :
    Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := C)) = 𝟙 _ := by
  have h₁ : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Qh (C := C)) = 𝟙 _ := rfl
  have h₂ : Functor.LaxMonoidal.ε (HomotopyCategory.quotient C (.up ℤ)) = 𝟙 _ := rfl
  have h₃ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  change (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Qh (C := C)) ≫
    _root_.DerivedCategory.Qh.map
      (Functor.LaxMonoidal.ε (HomotopyCategory.quotient C (.up ℤ)))) ≫ _ = _
  rw [h₁, h₂, h₃]
  erw [(_root_.DerivedCategory.Qh (C := C)).map_id, Category.comp_id, Category.comp_id]

private theorem normalize_unit_equation
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D) {X : C} {Y : D}
    (ε : X ⟶ X) (η : Y ⟶ Y) (a b : S.obj X ⟶ Y)
    (hε : ε = 𝟙 X) (hη : η = 𝟙 Y) (h : S.map ε ≫ a = b ≫ η) : b = a := by
  rw [hε, hη] at h
  erw [S.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

private theorem normalized_unit_formula
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, S.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : S.obj (𝟙_ _) ≅ 𝟙_ _)
    (h : Etale.ExceptionalCoefficients.UnitNormalizationAux F S rep e) :
    e.hom = rep (𝟙_ _) ≫ _root_.DerivedCategory.Q.map
      (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) := by
  exact normalize_unit_equation S _ _ _ _
    (derived_unit_epsilon C) (derived_unit_epsilon D) h

private theorem cochain_unit_to_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (U : D ⥤ C) [F.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : F ⊣ U) (S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (ad : S ⊣ U.mapDerivedCategory) (M : C) (N : D) (f : F.obj M ⟶ N) :
    (ad.homEquiv _ _).symm
      (_root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
        ((CochainComplex.singleFunctor C 0).obj M)) ≫
        U.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M))) ≫
      _root_.DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
          (HomologicalComplex.single D (.up ℤ) 0).map f) =
    (ad.homEquiv _ _).symm ((_root_.DerivedCategory.singleFunctor C 0).map
      (a.homEquiv _ _ f) ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app N) := by
  rw [Functor.map_comp, ← Category.assoc,
    ← CategoryTheory.single_adjunction_formula F U a S ad M]
  change (ad.homEquiv _ _).symm _ ≫
    (_root_.DerivedCategory.singleFunctor D 0).map f = _
  rw [← ad.homEquiv_naturality_right_symm]
  congr 1
  have hn := (U.mapDerivedCategorySingleFunctor 0).inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
  rw [Adjunction.homEquiv_unit]

private theorem representative_unit_insertion
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) (U : D ⥤ C) [F.Additive] [U.Additive] [F.OplaxMonoidal] [U.LaxMonoidal]
    [F.IsLeftAdjoint]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : F ⊣ U) (S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (ad : S ⊣ U.mapDerivedCategory)
    (hη : a.homEquiv _ _ (Functor.OplaxMonoidal.η F) = Functor.LaxMonoidal.ε U) :
    Etale.scalarAdjunctionRepresentativeMap F U a S ad (𝟙_ _) ≫
      _root_.DerivedCategory.Q.map (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) =
    (ad.homEquiv _ _).symm ((_root_.DerivedCategory.singleFunctor C 0).map
      (Functor.LaxMonoidal.ε U) ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app (𝟙_ _)) := by
  unfold Etale.scalarAdjunctionRepresentativeMap
  rw [← Etale.mapComplex_unit_formula, Functor.OplaxMonoidal.mapHomologicalComplexη]
  erw [cochain_unit_to_single F U a S ad (𝟙_ _) (𝟙_ _) (Functor.OplaxMonoidal.η F)]
  rw [hη]

private theorem single_unit_inv
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C] :
    (_root_.DerivedCategory.singleFunctorObjUnitIso C).inv = 𝟙 _ := by
  have h₁ : Functor.LaxMonoidal.ε (_root_.DerivedCategory.Qh (C := C)) = 𝟙 _ := rfl
  have h₂ : Functor.LaxMonoidal.ε (HomotopyCategory.quotient C (.up ℤ)) = 𝟙 _ := rfl
  have h₃ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  simp only [_root_.DerivedCategory.singleFunctorObjUnitIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, asIso_hom, Functor.Monoidal.εIso_hom, Iso.app_inv,
    h₁, h₂, h₃, _root_.DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv, NatTrans.id_app]
  erw [(_root_.DerivedCategory.Qh (C := C)).map_id, Category.comp_id, Category.comp_id,
    Category.id_comp]
  rfl

private theorem single_unit_hom
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C] :
    (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom = 𝟙 _ := by
  have h := (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom_inv_id
  rw [single_unit_inv] at h
  exact (Category.comp_id _).symm.trans h

/-- The representative-normalized unit is the transpose of the ordinary restriction unit,
after the canonical single/unit identifications.
Source: blueprint finite-dualizing normalization, paragraphs 1--3; the exact-single
adjunction formula and multiplication normalization.
Proof: the localization unit and single/unit comparisons are identities in the chosen
derived model. The representative normalization identifies the unit with localization of
the ordinary oplax unit. The cochain adjunction unit, the exact-single comparison, and
naturality identify its transpose with the single of the ordinary lax unit.
(blueprint: lem-coef-normalized-scalar-unit-single) -/
theorem normalizedUnit_singleAdjunction
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) (U : D ⥤ C) [F.Additive] [U.Additive] [F.OplaxMonoidal] [U.LaxMonoidal]
    [F.IsLeftAdjoint] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : F ⊣ U) (S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (ad : S ⊣ U.mapDerivedCategory)
    (rep : ∀ P : CochainComplex C ℤ, S.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : S.obj (𝟙_ _) ≅ 𝟙_ _)
    (h : Etale.ExceptionalCoefficients.UnitNormalizationAux F S rep e)
    (hrep : rep (𝟙_ _) = Etale.scalarAdjunctionRepresentativeMap F U a S ad (𝟙_ _))
    (hη : a.homEquiv _ _ (Functor.OplaxMonoidal.η F) = Functor.LaxMonoidal.ε U) :
    S.map (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom ≫ e.hom ≫
      (_root_.DerivedCategory.singleFunctorObjUnitIso D).inv =
    adjointInsertion U ad (Functor.LaxMonoidal.ε U) := by
  unfold adjointInsertion
  rw [single_unit_hom, single_unit_inv]
  erw [S.map_id, Category.id_comp, Category.comp_id]
  rw [normalized_unit_formula F S rep e h, hrep]
  exact representative_unit_insertion F U a S ad hη

end SheafExactDegreeZero
