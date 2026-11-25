/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Acyclicity in a tensored cone sequence

Source: Stacks Project, sites-cohomology.tex, Lemma 07A3, with the cone of Definition 06YN
(blueprint: lem-pc-kflat-tensor-cone-two-out-of-three).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- A local abbreviation for the existing category of modules over the ring sheaf. -/
abbrev moduleCategory :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

noncomputable local instance : MonoidalCategory (moduleCategory R) := monoidalCategory R

/-- (blueprint: lem-pc-kflat-tensor-cone-two-out-of-three) Stacks Project, Lemma 07A3.
The cone comparison for the total tensor complex identifies tensoring the cone of `f`
with the cone of the induced tensor map. The cone triangle is distinguished in the
homotopy category; since acyclic complexes form a triangulated subcategory, any two
acyclic total tensor complexes force the third to be acyclic. -/
theorem tensor_mappingCone_two_out_of_three :
    ∀ (A K₁ K₂ : CochainComplex (moduleCategory R) ℤ) (f : K₁ ⟶ K₂),
      A.Acyclic →
      (∃ e : CochainComplex.mapBifunctor A (CochainComplex.mappingCone f)
          (curriedTensor (moduleCategory R)) ≅
          CochainComplex.mappingCone
            (HomologicalComplex.mapBifunctorMap (𝟙 A) f (curriedTensor (moduleCategory R)) (.up ℤ)),
        HomologicalComplex.mapBifunctorMap (𝟙 A) (CochainComplex.mappingCone.inr f)
            (curriedTensor (moduleCategory R)) (.up ℤ) ≫ e.hom =
          CochainComplex.mappingCone.inr
            (HomologicalComplex.mapBifunctorMap (𝟙 A) f
              (curriedTensor (moduleCategory R)) (.up ℤ))) ∧
      ((A.mapBifunctor K₁ (curriedTensor (moduleCategory R))).Acyclic ∧
          (A.mapBifunctor K₂ (curriedTensor (moduleCategory R))).Acyclic →
        (A.mapBifunctor (CochainComplex.mappingCone f)
          (curriedTensor (moduleCategory R))).Acyclic) ∧
      ((A.mapBifunctor K₁ (curriedTensor (moduleCategory R))).Acyclic ∧
          (A.mapBifunctor (CochainComplex.mappingCone f)
            (curriedTensor (moduleCategory R))).Acyclic →
        (A.mapBifunctor K₂ (curriedTensor (moduleCategory R))).Acyclic) ∧
      ((A.mapBifunctor K₂ (curriedTensor (moduleCategory R))).Acyclic ∧
          (A.mapBifunctor (CochainComplex.mappingCone f)
            (curriedTensor (moduleCategory R))).Acyclic →
        (A.mapBifunctor K₁ (curriedTensor (moduleCategory R))).Acyclic) := by
  intro A K₁ K₂ f _hA
  have : MonoidalPreadditive (moduleCategory R) := (tensorClosed R).1.some
  let g := HomologicalComplex.mapBifunctorMap (𝟙 A) f
    (curriedTensor (moduleCategory R)) (.up ℤ)
  let e := CochainComplex.mapBifunctorMappingCone₂Iso A f
    (curriedTensor (moduleCategory R))
  let P := HomotopyCategory.subcategoryAcyclic (moduleCategory R)
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished g
  have he : P ((HomotopyCategory.quotient _ _).obj
      (A.mapBifunctor (CochainComplex.mappingCone f) (curriedTensor (moduleCategory R)))) ↔
      P ((HomotopyCategory.quotient _ _).obj (CochainComplex.mappingCone g)) := by
    exact ⟨fun h ↦ P.prop_of_iso ((HomotopyCategory.quotient _ _).mapIso e) h,
      fun h ↦ P.prop_of_iso ((HomotopyCategory.quotient _ _).mapIso e.symm) h⟩
  refine ⟨⟨e, CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom A f
    (curriedTensor (moduleCategory R))⟩, ?_, ?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h₁ h₂ ⊢
    apply he.mpr
    exact P.ext_of_isTriangulatedClosed₃ _ hT h₁ h₂
  · rintro ⟨h₁, h₃⟩
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h₁ h₃ ⊢
    exact P.ext_of_isTriangulatedClosed₂ _ hT h₁ (he.mp h₃)
  · rintro ⟨h₂, h₃⟩
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h₂ h₃ ⊢
    exact P.ext_of_isTriangulatedClosed₁ _ hT h₂ (he.mp h₃)

end SheafOfModules
