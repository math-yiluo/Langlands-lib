/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # ComplexLiftConeProperties

Source: Stacks Project, Tag 0BCA.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Properties of the actual cone of a reduced quasi-isomorphism.

Source: Stacks Project, Tag 0BCA, cone construction paragraph.
(blueprint: lem-sc-complex-lift-cone-properties).

Proof: The cone of a quasi-isomorphism is acyclic by the long exact homology
sequence of its triangle. If E vanishes above e and K above k, its terms vanish
above max e k: its term in degree i is E in degree i+1 plus the reduction of K
in degree i. Choose a class member reducing to E in degree i+1. The product of
that member with K in degree i belongs to the class by the forward direction
of the sum-closure equivalence. Extension of scalars preserves binary
biproducts, so this product reduces to the stated cone term. -/
theorem complex_lift_cone_properties
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (hKbound : ∃ b : ℤ, K.IsStrictlyLE b)
    (hKterms : ∀ i : ℤ, K.X i ∈ Pclass)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEterms : ∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
      Nonempty (E.X i ≅ (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P))
    (δ : E ⟶ ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) [QuasiIso δ] :
    (∃ b : ℤ, (CochainComplex.mappingCone δ).IsStrictlyLE b) ∧
      (CochainComplex.mappingCone δ).Acyclic ∧
      ∀ i : ℤ, ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
        Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P ≅
          (CochainComplex.mappingCone δ).X i) := by
  classical
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  obtain ⟨bK, hbK⟩ := hKbound
  obtain ⟨bE, hbE⟩ := hEbound
  let := hbK
  let := hbE
  refine ⟨⟨max bK bE, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩, ?_, ?_⟩
  · intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · exact E.isZero_of_isStrictlyLE bE (i + 1) (by omega)
    · exact F.map_isZero (K.isZero_of_isStrictlyLE bK i (by omega))
  · let D := ModuleCat.{max u v} (R ⧸ I)
    apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
    apply ((HomotopyCategory.subcategoryAcyclic D).trW_iff_of_distinguished
      (CochainComplex.mappingCone.triangleh δ)
      (HomotopyCategory.mappingCone_triangleh_distinguished δ)).mp
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff δ).mpr
      (show HomologicalComplex.quasiIso D (ComplexShape.up ℤ) δ from (inferInstance : QuasiIso δ))
  · intro i
    obtain ⟨P, hP, ⟨eP⟩⟩ := hEterms (i + 1)
    let Q := Limits.biprod P (K.X i)
    have hQ : Q ∈ Pclass :=
      ((hclosed P (K.X i) Q ⟨ModuleCat.biprodIsoProd P (K.X i)⟩).mpr
        ⟨hP, hKterms i⟩).2
    refine ⟨Q, hQ, ⟨?_⟩⟩
    exact F.mapBiprod P (K.X i) ≪≫
      Limits.biprod.mapIso eP.symm (Iso.refl _) ≪≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod δ i (i + 1) rfl).symm


end AlgebraicGeometry
