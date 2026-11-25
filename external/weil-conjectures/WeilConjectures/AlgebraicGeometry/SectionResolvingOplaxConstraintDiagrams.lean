/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxInternalConjugation
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxModelEdges
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxUnitModels

/-! # Resolving models of the derived oplax constraint diagrams

Source: Stacks Project, Tags 07A4 and 0G7E; the prescribed six edge squares are
composed with their common vertex comparisons, and the ordinary cochain
associator equation identifies the resulting paths.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d va vb vc vd
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace ResolvingOplaxConstraints

section PathComposition
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
  (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q))
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
  (μ : ∀ M N : C, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)

private theorem paths_of_edges (P Q H : A)
    (hi : VertexInvertibility F L q r s t ε P Q H)
    (he : EdgeIdentification F L q r s t ε β μ P Q H)
    (hc : F.map (α_ P Q H).hom ≫ β P (Q ⊗ H) ≫ F.obj P ◁ β Q H =
      β (P ⊗ Q) H ≫ β P Q ▷ F.obj H ≫
        (α_ (F.obj P) (F.obj Q) (F.obj H)).hom) :
    AssociativityPaths F L q r s t ε β μ P Q H := by
  rcases he with ⟨h01, h12, h23, h04, h45, h53⟩
  have hupper : upperPath L μ (q.obj P) (q.obj Q) (q.obj H) ≫
      vertex3 F L q r t ε P Q H =
      vertex0 F L q r s ε P Q H ≫ r.map
        (F.map (α_ P Q H).hom ≫ β P (Q ⊗ H) ≫ F.obj P ◁ β Q H) := by
    simp only [upperPath, Functor.map_comp, Category.assoc,
      h23, reassoc_of% h12, reassoc_of% h01]
  have hlower : lowerPath L μ (q.obj P) (q.obj Q) (q.obj H) ≫
      vertex3 F L q r t ε P Q H =
      vertex0 F L q r s ε P Q H ≫ r.map
        (β (P ⊗ Q) H ≫ β P Q ▷ F.obj H ≫
          (α_ (F.obj P) (F.obj Q) (F.obj H)).hom) := by
    simp only [lowerPath, Functor.map_comp, Category.assoc,
      h53, reassoc_of% h45, reassoc_of% h04]
  refine ⟨hupper, hlower, ?_⟩
  have : IsIso (vertex3 F L q r t ε P Q H) := hi.2.2.2.1
  apply (cancel_mono (vertex3 F L q r t ε P Q H)).1
  rw [hupper, hlower, hc]

variable (unit : F.obj (𝟙_ A) ⟶ 𝟙_ B)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B))

private theorem units_of_edges (P : A)
    (he : UnitEdgeIdentification F L q r s t ε β unit eA eB μ v P)
    (hl : β (𝟙_ A) P ≫ unit ▷ F.obj P ≫ (λ_ (F.obj P)).hom = F.map (λ_ P).hom)
    (hr : β P (𝟙_ A) ≫ F.obj P ◁ unit ≫ (ρ_ (F.obj P)).hom = F.map (ρ_ P).hom) :
    UnitIdentification F L q r s t ε β unit eA eB μ v P := by
  rcases he with ⟨hi0, hi1, hi2, hi3, h01, h12, h23, h03,
    hj0, hj1, hj2, hj3, k01, k12, k23, k03⟩
  have hleft : leftUnitPath L q r eB μ v (q.obj P) ≫ ε.app P =
      pairModel F L q r s ε (𝟙_ A) P ≫
        r.map (β (𝟙_ A) P ≫ unit ▷ F.obj P ≫ (λ_ (F.obj P)).hom) := by
    simp only [leftUnitPath, Functor.map_comp, Category.assoc,
      h23, reassoc_of% h12, reassoc_of% h01]
  have hright : rightUnitPath L q r eB μ v (q.obj P) ≫ ε.app P =
      pairModel F L q r s ε P (𝟙_ A) ≫
        r.map (β P (𝟙_ A) ≫ F.obj P ◁ unit ≫ (ρ_ (F.obj P)).hom) := by
    simp only [rightUnitPath, Functor.map_comp, Category.assoc,
      k23, reassoc_of% k12, reassoc_of% k01]
  have : IsIso (ε.app P) := hi3
  have hleft_eq : leftUnitPath L q r eB μ v (q.obj P) =
      L.map (regularLeft q eA (q.obj P)) := by
    apply (cancel_mono (ε.app P)).1
    rw [hleft, hl]
    exact h03.symm
  have hright_eq : rightUnitPath L q r eB μ v (q.obj P) =
      L.map (regularRight q eA (q.obj P)) := by
    apply (cancel_mono (ε.app P)).1
    rw [hright, hr]
    exact k03.symm
  exact ⟨hi0, hi1, hi2, hi3, h01, h12, h23, hleft, h03, hleft_eq,
    hj0, hj1, hj2, hj3, k01, k12, k23, hright, k03, hright_eq⟩

end PathComposition

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] qTensor tensorComparison totalComparison

private theorem section_vertices_of_resolving {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q H : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory)
    (hc : ResolvingClosure Λ f P.obj Q.obj H.obj) :
    SectionVertices Λ f P.obj Q.obj H.obj := by
  let := derivedMonoidal Λ Y
  let := derivedMonoidal Λ X
  have hY (A B : CochainComplex (modules Λ Y) ℤ)
      (hAB : A.IsKFlatIndependentCoefficients ∨ B.IsKFlatIndependentCoefficients) :
      IsIso (modelTensor Λ Y A B) :=
    by simpa only [modelTensor, qTensor] using
      (tensor_representatives Λ Y).exists.choose_spec.2.1 A B hAB
  have hX (A B : CochainComplex (modules Λ X) ℤ)
      (hAB : A.IsKFlatIndependentCoefficients ∨ B.IsKFlatIndependentCoefficients) :
      IsIso (modelTensor Λ X A B) :=
    by simpa only [modelTensor, qTensor] using
      (tensor_representatives Λ X).exists.choose_spec.2.1 A B hAB
  have hFP : CochainComplex.IsKFlatIndependentCoefficients
      ((totalSectionPull Λ f).obj P.obj) :=
    (hc.2 P.obj (by simp)).1
  have hFQ : CochainComplex.IsKFlatIndependentCoefficients
      ((totalSectionPull Λ f).obj Q.obj) :=
    (hc.2 Q.obj (by simp)).1
  have hFH : CochainComplex.IsKFlatIndependentCoefficients
      ((totalSectionPull Λ f).obj H.obj) :=
    (hc.2 H.obj (by simp)).1
  have := hY P.obj Q.obj (Or.inl P.property.1)
  have := hY (P.obj ⊗ Q.obj) H.obj (Or.inr H.property.1)
  have := hY Q.obj H.obj (Or.inl Q.property.1)
  have := hY P.obj (Q.obj ⊗ H.obj) (Or.inl P.property.1)
  have := hX ((totalSectionPull Λ f).obj P.obj)
    ((totalSectionPull Λ f).obj Q.obj) (Or.inl hFP)
  have := hX (((totalSectionPull Λ f).obj P.obj) ⊗ ((totalSectionPull Λ f).obj Q.obj))
    ((totalSectionPull Λ f).obj H.obj) (Or.inr hFH)
  have := hX ((totalSectionPull Λ f).obj Q.obj)
    ((totalSectionPull Λ f).obj H.obj) (Or.inl hFQ)
  have := hX ((totalSectionPull Λ f).obj P.obj)
    (((totalSectionPull Λ f).obj Q.obj) ⊗ ((totalSectionPull Λ f).obj H.obj)) (Or.inl hFP)
  have := hX ((totalSectionPull Λ f).obj P.obj)
    ((totalSectionPull Λ f).obj (Q.obj ⊗ H.obj)) (Or.inl hFP)
  have := hX ((totalSectionPull Λ f).obj (P.obj ⊗ Q.obj))
    ((totalSectionPull Λ f).obj H.obj) (Or.inr hFH)
  dsimp only [SectionVertices, VertexInvertibility, vertex0, vertex1, vertex2, vertex3,
    vertex4, vertex5, leftModel, rightModel, pairModel]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Resolving-model identification of derived oplax constraint diagrams.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E;
explicit representative diagram calculation
(auxiliary; not a blueprint node).

Proof: take resolving closure and the six edge squares from the model-edge
calculation. All six vertex maps are invertible by the one-sided K-flat tensor
comparison and the resolution isomorphism. Compose each branch's edge squares;
the ordinary cochain associator equation identifies their localized middle paths.
Cancel the common final vertex comparison. For each unit compose the three edge
squares, use the ordinary cochain unit equation, and cancel the final resolution
comparison. Finally apply the separate fixed internal conjugation calculation. -/
theorem section_resolving_oplax_constraint_diagrams {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v) :
    (∀ P Q H : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
      ResolvingClosure Λ f P.obj Q.obj H.obj ∧
        SectionVertices Λ f P.obj Q.obj H.obj ∧
        SectionEdges Λ f μ P.obj Q.obj H.obj ∧
        SectionAssociativity Λ f μ P.obj Q.obj H.obj) ∧
    (∀ P : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
      SectionUnits Λ f μ v P.obj) ∧
    (∀ (δ : InternalTensorArrow Λ f)
      (w : (internalDerivedPullback Λ f).obj
          (𝟙_ (DerivedCategory (internalModules Λ Y))) ⟶
        𝟙_ (DerivedCategory (internalModules Λ X))),
      Conjugation Λ f μ v δ w →
        (∀ M N H : DerivedCategory (internalModules Λ Y), InternalEdges Λ f μ δ M N H) ∧
        (∀ M : DerivedCategory (internalModules Λ Y), InternalUnits Λ f μ v δ w M)) := by
  let := derivedMonoidal Λ Y
  let := derivedMonoidal Λ X
  refine ⟨?_, ?_, section_resolving_oplax_internal_conjugation Λ f μ v h⟩
  · intro P Q H
    obtain ⟨hclosure, hedges⟩ :=
      section_resolving_oplax_model_edges Λ f μ v h P Q H
    have hvertices := section_vertices_of_resolving Λ f P Q H hclosure
    refine ⟨hclosure, hvertices, hedges, ?_⟩
    apply paths_of_edges _ _ _ _ _ _ _ _ _ P.obj Q.obj H.obj hvertices hedges
    exact (section_oplax_total_comparison Λ f).2.2.2.2.2.2.2.2.2.1 P.obj Q.obj H.obj |>.1
  · intro P
    apply units_of_edges _ _ _ _ _ _ _ _ _ _ _ _ _ P.obj
      (section_resolving_oplax_unit_models Λ f μ v h P)
    · exact (section_oplax_total_comparison Λ f).2.2.2.2.2.2.2.2.2.2.1 P.obj |>.1
    · exact (section_oplax_total_comparison Λ f).2.2.2.2.2.2.2.2.2.2.2 P.obj |>.1

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
