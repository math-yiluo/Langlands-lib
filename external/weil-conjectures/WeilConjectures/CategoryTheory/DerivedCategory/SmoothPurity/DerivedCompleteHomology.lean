/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Derived completeness passes to cohomology
Source: Stacks Project, Tag 091P, the Roos product criterion.
(blueprint: lem-weil-derived-complete-homology). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

private lemma module_countableAB4Star {A : Type u} [CommRing A] :
    CountableAB4Star (ModuleCat.{v} A) := by
  let F := forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}
  let : F.PreservesEpimorphisms := ⟨fun {X Y} f _ ↦ by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact (ModuleCat.epi_iff_surjective f).mp inferInstance⟩
  let := Functor.preservesHomology_of_preservesEpis_and_kernels F
  let := Functor.preservesFiniteColimits_of_preservesHomology F
  exact ⟨fun J ↦ HasExactLimitsOfShape.domain_of_functor (Discrete J) F⟩

private lemma complete_iff_isIso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    [HasCountableProducts (DerivedCategory (ModuleCat.{v} A))]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A)) :
    IsDerivedComplete I K ↔ ∀ f ∈ I,
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K)) := by
  constructor
  · intro h f hf
    obtain ⟨L, p, δ, hT⟩ := distinguished_cocone_triangle₁
      (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K))
    exact (Triangle.isZero₁_iff_isIso₂ _ hT).mp (h f hf L ⟨p, δ, hT⟩)
  · intro h f hf _ L ⟨p, δ, hT⟩
    exact (Triangle.isZero₁_iff_isIso₂ _ hT).mpr (h f hf)

private lemma map_tower_isIso
    {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R]
    [HasCountableProducts C] [HasCountableProducts D]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (X : C) (f : R)
    (h : IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ X) (fun _ ↦ f • 𝟙 X))) :
    IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ F.obj X) (fun _ ↦ f • 𝟙 (F.obj X))) := by
  let e := PreservesProduct.iso F (fun _ : ℕ ↦ X)
  let t := towerTransitionEndomorphism (K := fun _ : ℕ ↦ X) (fun _ ↦ f • 𝟙 X)
  have he : F.map t ≫ e.hom = e.hom ≫ towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ F.obj X) (fun _ ↦ f • 𝟙 (F.obj X)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, e, PreservesProduct.iso_hom, piComparison_comp_π]
    simp [t, towerTransitionEndomorphism, towerProductShift,
      ← F.map_comp, Functor.map_sub, Functor.map_smul]
  have ht : towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ F.obj X) (fun _ ↦ f • 𝟙 (F.obj X)) =
      e.inv ≫ F.map t ≫ e.hom := by
    rw [he, Iso.inv_hom_id_assoc]
  let := h
  rw [ht]
  infer_instance

/-- Cohomology modules of a derived-complete complex are derived complete.
Source: Stacks Project, Tag 091P, the equivalent Roos product criterion.
(blueprint: lem-weil-derived-complete-homology).
Proof: completeness says that one minus the multiplication shift is invertible on
countable products. Exact products of modules commute with homology. Therefore the
same operator is invertible on the product of each cohomology module. The degree-zero
single functor preserves those products and scalar multiplication, so the Roos
criterion gives derived completeness of that module. -/
theorem isDerivedComplete_homology {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDerivedComplete I K) (i : ℤ) :
    ModuleCat.IsDerivedComplete I ((homologyFunctor (ModuleCat.{v} A) i).obj K) := by
  let := module_countableAB4Star.{u, v} (A := A)
  let := derivedCategory_hasCountableProducts (ModuleCat.{v} A)
  let H := homologyFunctor (ModuleCat.{v} A) i
  let S := singleFunctor (ModuleCat.{v} A) 0
  have hH : PreservesLimitsOfShape (Discrete ℕ) H :=
    (derivedCategory_countableProducts_core (ModuleCat.{v} A)).choose_spec.2 ℕ i
  have hQ : PreservesLimitsOfShape (Discrete ℕ) (Q (C := ModuleCat.{v} A)) := by
    let h (C : ℕ → CochainComplex (ModuleCat.{v} A) ℤ) :
        PreservesLimit (Discrete.functor C) Q :=
      preservesLimit_of_preserves_limit_cone (limit.isLimit _)
        ((derivedCategory_countableProducts_core (ModuleCat.{v} A)).choose_spec.1 ℕ C).some
    exact preservesLimitsOfShape_of_discrete Q
  have hS : PreservesLimitsOfShape (Discrete ℕ) S := by
    have hSingle : PreservesLimitsOfShape (Discrete ℕ)
        (CochainComplex.singleFunctor (ModuleCat.{v} A) 0) := by
      change PreservesLimitsOfShape (Discrete ℕ)
        (HomologicalComplex.single (ModuleCat.{v} A) (.up ℤ) 0)
      infer_instance
    exact preservesLimitsOfShape_of_natIso (singleFunctorIsoCompQ (ModuleCat.{v} A) 0).symm
  have hSC : (HomologicalComplex.shortComplexFunctor
      (ModuleCat.{v} A) (.up ℤ) i).Linear A := ⟨by intros; rfl⟩
  have hCH : (HomologicalComplex.homologyFunctor
      (ModuleCat.{v} A) (.up ℤ) i).Linear A :=
    Functor.linear_of_iso _
      (HomologicalComplex.homologyFunctorIso (ModuleCat.{v} A) (.up ℤ) i).symm
  have hHL : H.Linear A := by
    let : Localization.Lifting Q
        (HomologicalComplex.quasiIso (ModuleCat.{v} A) (.up ℤ))
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (.up ℤ) i) H :=
      ⟨homologyFunctorFactors (ModuleCat.{v} A) i⟩
    exact (Localization.functor_linear_iff Q
      (HomologicalComplex.quasiIso (ModuleCat.{v} A) (.up ℤ)) A
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (.up ℤ) i) H).mp hCH
  apply (complete_iff_isIso I (S.obj (H.obj K))).mpr
  intro f hf
  exact map_tower_isIso S _ f
    (map_tower_isIso H K f ((complete_iff_isIso I K).mp hK f hf))

end DerivedCategory
