/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-! # K-flat cone presentations of distinguished triangles

Source: Stacks Project, Tag 06Y4; Mathlib's cone presentation of
triangles in the derived category.
(blueprint: lem-pc-kflat-cone-triangle-presentation).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

/-- Every distinguished triangle of modules has a K-flat mapping-cone presentation.

Source: Stacks Project, Tag 06Y4 (K-flat resolutions), and
`DerivedCategory.mem_distTriang_iff`.

Proof: write the triangle as the derived image of the cone of a chain map X to Y.
Apply the functorial flat resolution to both complexes and to that map. The two
resolution maps are quasi-isomorphisms and their naturality gives a commuting
square. In the derived category they give isomorphisms on the first two vertices;
the distinguished-triangle axiom extends these to an isomorphism of triangles.
The resolved complexes are K-flat. Convert this to preservation of acyclic
tensors. For an acyclic V, tensoring the cone with V identifies with the cone
of the tensor map, whose first two objects are acyclic. The triangulated
subcategory of acyclic complexes therefore contains that cone, proving the
third displayed condition.
No boundedness or nonzero-ring hypothesis is used.
(blueprint: lem-pc-kflat-cone-triangle-presentation). -/
theorem exists_kFlat_cone_triangle_presentation
    (A : Type u) [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) :
    ∃ (P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ) (f : P₁ ⟶ P₂),
      (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V P₁ (curriedTensor _)).Acyclic) ∧
      (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V P₂ (curriedTensor _)).Acyclic) ∧
      (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V (CochainComplex.mappingCone f)
          (curriedTensor _)).Acyclic) ∧
      Nonempty (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ≅
        T) := by
  classical
  have (X Y : GradedObject ℤ (ModuleCat.{u} A)) : X.HasTensor Y := inferInstance
  have (X Y Z : GradedObject ℤ (ModuleCat.{u} A)) :
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
  have (X Y Z : GradedObject ℤ (ModuleCat.{u} A)) :
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
  have (X Y Z W : GradedObject ℤ (ModuleCat.{u} A)) :
      GradedObject.HasTensor₄ObjExt X Y Z W := inferInstance
  have (M : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight M))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  obtain ⟨X, Y, g, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).1 hT
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} A))).reduced
  let P₁ := Λ.resolutionFunctor.obj X
  let P₂ := Λ.resolutionFunctor.obj Y
  let f := Λ.resolutionFunctor.map g
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
  have h₁ : W.kFlat P₁ :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le X
  have h₂ : W.kFlat P₂ :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le Y
  have hac (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : W.kFlat P)
      (V : CochainComplex (ModuleCat.{u} A) ℤ) (hV : V.Acyclic) :
      (CochainComplex.mapBifunctor V P (curriedTensor _)).Acyclic := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic] at hP
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (hP _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic V).2 hV)).2
  have hc (V : CochainComplex (ModuleCat.{u} A) ℤ) (hV : V.Acyclic) :
      (CochainComplex.mapBifunctor V (CochainComplex.mappingCone f)
        (curriedTensor _)).Acyclic := by
    let g' := HomologicalComplex.mapBifunctorMap (𝟙 V) f (curriedTensor _) (.up ℤ)
    let e' := CochainComplex.mapBifunctorMappingCone₂Iso V f (curriedTensor _)
    have hh₁ := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
      (hac P₁ h₁ V hV)
    have hh₂ := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
      (hac P₂ h₂ V hV)
    have hh₃ := (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} A))
      |>.ext_of_isTriangulatedClosed₃ _
        (HomotopyCategory.mappingCone_triangleh_distinguished g') hh₁ hh₂
    have hcone := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hh₃
    intro j
    exact (hcone j).of_iso e'.symm
  refine ⟨P₁, P₂, f, hac P₁ h₁, hac P₂ h₂, hc, ⟨?_⟩⟩
  let e₁ := asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app X))
  let e₂ := asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app Y))
  refine (Pretriangulated.isoTriangleOfIso₁₂ _ _
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g) e₁ e₂ ?_) ≪≫ e.symm
  change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (Λ.resolutionNatTrans.app Y) =
    DerivedCategory.Q.map (Λ.resolutionNatTrans.app X) ≫ DerivedCategory.Q.map g
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (Λ.resolutionNatTrans.naturality g)

end ModuleCat
