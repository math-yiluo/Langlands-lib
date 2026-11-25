/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.AlgebraicGeometry.SectionLocalizationAssociativity
import WeilConjectures.AlgebraicGeometry.SectionRepresentativeTensorArrow
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Six resolving oplax model edge squares

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E;
the six edge-identification part of `lem-pd-section-resolving-oplax-model-edges`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d va vb vc vd
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace ResolvingOplaxConstraints

section EdgeCalculus
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
  (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q))
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
  (μ : MonoidalCategory.tensor C ⋙ L ⟶ L.prod L ⋙ MonoidalCategory.tensor D)
  (hp : ∀ P Q, μ.app (q.obj P, q.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫
    t (F.obj P) (F.obj Q) =
      L.map (s P Q) ≫ ε.app (P ⊗ Q) ≫ r.map (β P Q))
  (hs : ∀ P Q H, (α_ (q.obj P) (q.obj Q) (q.obj H)).hom ≫
      q.obj P ◁ s Q H ≫ s P (Q ⊗ H) =
    s P Q ▷ q.obj H ≫ s (P ⊗ Q) H ≫ q.map (α_ P Q H).hom)
  (ht : ∀ P Q H, (α_ (r.obj P) (r.obj Q) (r.obj H)).hom ≫
      r.obj P ◁ t Q H ≫ t P (Q ⊗ H) =
    t P Q ▷ r.obj H ≫ t (P ⊗ Q) H ≫ r.map (α_ P Q H).hom)
  (htn : ∀ {P P' Q Q'} (a : P ⟶ P') (b : Q ⟶ Q'),
    (r.map a ⊗ₘ r.map b) ≫ t P' Q' = t P Q ≫ r.map (a ⊗ₘ b))

include hp hs ht htn in
private theorem edge_calculus (P Q H : A) :
    EdgeIdentification F L q r s t ε β (fun M N ↦ μ.app (M, N)) P Q H := by
  dsimp only [EdgeIdentification, vertex0, vertex1, vertex2, vertex3,
    vertex4, vertex5, leftModel, rightModel, pairModel, Functor.comp_obj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tensorHom_id, id_tensorHom, Functor.map_comp, Category.assoc]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc (α_ (q.obj P) (q.obj Q) (q.obj H)).hom,
      hs, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    erw [ε.naturality (α_ P Q H).hom]
    rfl
  · have hn := μ.naturality (Prod.mkHom (𝟙 (q.obj P)) (s Q H))
    dsimp at hn
    simp only [L.map_id, id_tensorHom] at hn
    erw [← whiskerLeft_comp_tensorHom, Category.assoc, ← reassoc_of% hn, hp]
    simp only [id_tensorHom, Functor.map_comp, Category.assoc]
  · simp only [id_tensorHom, Category.assoc]
    erw [whiskerLeft_comp_tensorHom_assoc,
      tensorHom_comp_whiskerLeft_assoc (ε.app P)]
    simp only [Category.assoc]
    erw [hp, tensorHom_comp_comp_comp]
    simp only [Category.assoc]
    have hn := htn (𝟙 (F.obj P)) (β Q H)
    simp only [r.map_id, id_tensorHom] at hn
    erw [hn, whiskerLeft_comp_tensorHom_assoc]
  · have hn := μ.naturality (Prod.mkHom (s P Q) (𝟙 (q.obj H)))
    dsimp at hn
    simp only [L.map_id, tensorHom_id] at hn
    erw [← whiskerRight_comp_tensorHom, Category.assoc, ← reassoc_of% hn, hp]
    simp only [tensorHom_id, Functor.map_comp, Category.assoc]
  · simp only [tensorHom_id, Category.assoc]
    erw [whiskerRight_comp_tensorHom_assoc,
      tensorHom_comp_whiskerRight_assoc _ _ (ε.app H)]
    simp only [Category.assoc]
    erw [hp, comp_tensorHom_comp_comp]
    simp only [Category.assoc]
    have hn := htn (β P Q) (𝟙 (F.obj H))
    simp only [r.map_id, tensorHom_id] at hn
    erw [hn, whiskerRight_comp_tensorHom_assoc]
  · simp only [id_tensorHom, tensorHom_id, Category.assoc]
    erw [← associator_naturality_assoc, ht]

private theorem representative_extension
    (htn' : ∀ {P P' Q Q'} (a : P ⟶ P') (b : Q ⟶ Q'),
      (r.map a ⊗ₘ r.map b) ≫ t P' Q' = t P Q ≫ r.map (a ⊗ₘ b))
    (hsn : ∀ {P P' Q Q'} (a : P ⟶ P') (b : Q ⟶ Q'),
      (q.map a ⊗ₘ q.map b) ≫ s P' Q' = s P Q ≫ q.map (a ⊗ₘ b))
    (hβn : ∀ {P P' Q Q'} (a : P ⟶ P') (b : Q ⟶ Q'),
      F.map (a ⊗ₘ b) ≫ β P' Q' = β P Q ≫ (F.map a ⊗ₘ F.map b))
    (R : A → Prop)
    (res : ∀ P, ∃ (A : A) (a : A ⟶ P), R A ∧ IsIso (q.map a))
    (hrep : ∀ P Q, R P → R Q →
      μ.app (q.obj P, q.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫ t (F.obj P) (F.obj Q) =
        L.map (s P Q) ≫ ε.app (P ⊗ Q) ≫ r.map (β P Q))
    (P Q : A) :
    μ.app (q.obj P, q.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫ t (F.obj P) (F.obj Q) =
      L.map (s P Q) ≫ ε.app (P ⊗ Q) ≫ r.map (β P Q) := by
  let sn : q.prod q ⋙ MonoidalCategory.tensor C ⟶ MonoidalCategory.tensor A ⋙ q :=
    { app := fun Z ↦ s Z.1 Z.2
      naturality := by
        rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨a, b⟩
        exact hsn a b }
  let tn : r.prod r ⋙ MonoidalCategory.tensor D ⟶ MonoidalCategory.tensor B ⋙ r :=
    { app := fun Z ↦ t Z.1 Z.2
      naturality := by
        rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨a, b⟩
        exact htn' a b }
  let bn : MonoidalCategory.tensor A ⋙ F ⟶ F.prod F ⋙ MonoidalCategory.tensor B :=
    { app := fun Z ↦ β Z.1 Z.2
      naturality := by
        rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨a, b⟩
        exact hβn a b }
  let l : q.prod q ⋙ MonoidalCategory.tensor C ⋙ L ⟶
      F.prod F ⋙ MonoidalCategory.tensor B ⋙ r :=
    Functor.whiskerLeft (q.prod q) μ ≫
      Functor.whiskerRight (NatTrans.prod ε ε) (MonoidalCategory.tensor D) ≫
      Functor.whiskerLeft (F.prod F) tn
  let k : q.prod q ⋙ MonoidalCategory.tensor C ⋙ L ⟶
      F.prod F ⋙ MonoidalCategory.tensor B ⋙ r :=
    Functor.whiskerRight sn L ≫
      Functor.whiskerLeft (MonoidalCategory.tensor A) ε ≫ Functor.whiskerRight bn r
  have heq : l = k := by
    apply NatTrans.ext
    funext Z
    obtain ⟨A, a, hA, ha⟩ := res Z.1
    obtain ⟨B, b, hB, hb⟩ := res Z.2
    have := ha
    have := hb
    have : IsIso (Prod.mkHom (q.map a) (q.map b)) :=
      (isIso_prod_iff (f := Prod.mkHom (q.map a) (q.map b))).mpr
        ⟨inferInstance, inferInstance⟩
    have : IsIso ((q.prod q ⋙ MonoidalCategory.tensor C ⋙ L).map (Prod.mkHom a b)) := by
      change IsIso (L.map ((MonoidalCategory.tensor C).map
        (Prod.mkHom (q.map a) (q.map b))))
      infer_instance
    apply (cancel_epi ((q.prod q ⋙ MonoidalCategory.tensor C ⋙ L).map
      (Prod.mkHom a b))).mp
    rw [l.naturality, k.naturality]
    have hlk : l.app (A, B) = k.app (A, B) := by
      simpa only [l, k, sn, tn, bn, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.prod,
        Functor.comp_obj, Functor.prod_obj, MonoidalCategory.tensor_obj,
        MonoidalCategory.tensor_map, Category.assoc] using hrep A B hA hB
    rw [hlk]
  simpa only [l, k, sn, tn, bn, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.prod,
    Functor.comp_obj, Functor.prod_obj, MonoidalCategory.tensor_obj,
    MonoidalCategory.tensor_map, Category.assoc] using NatTrans.congr_app heq (P, Q)

end EdgeCalculus

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] qTensor tensorComparison totalComparison

private theorem section_resolution (T : Scheme.{u})
    (P : CochainComplex (modules Λ T) ℤ) :
    ∃ (R : CochainComplex (modules Λ T) ℤ) (r : R ⟶ P),
      KFlatSectionComparison.sectionResolving Λ T R ∧ QuasiIso r := by
  let E := (equivalence Λ T).mapHomologicalComplex (.up ℤ)
  obtain ⟨R, r, hr, hf, hk⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (E.inverse.obj P)
  have hki : KFlatSectionComparison.internalResolving Λ T R := by
    refine ⟨?_, fun n ↦ (hf n).2⟩
    intro A hA
    have h := ((HomotopyCategory.kFlat_iff_preserves_acyclic _).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff R).mpr hk)
      ((HomotopyCategory.quotient _ _).obj A)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic A).mpr hA)).2
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp h
  refine ⟨E.functor.obj R, E.functor.map r ≫ E.counitIso.hom.app P, ?_, ?_⟩
  · exact (KFlatSectionComparison.section_kflat_tensor_comparison.{u, 0, 0} Λ T).2.1 R |>.mp hki
  · have : QuasiIso (E.functor.map r) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology r (equivalence Λ T).functor
    infer_instance

private theorem section_tensor_map (T : Scheme.{u})
    {M M' N N' : DerivedCategory (modules Λ T)} (a : M ⟶ M') (b : N ⟶ N') :
    (tensor Λ T).map (Prod.mkHom a b) =
      @MonoidalCategoryStruct.tensorHom _ _ (derivedMonoidal Λ T).toMonoidalCategoryStruct
        M M' N N' a b := by
  rfl

attribute [local irreducible] Functor.mapDerivedCategory

private theorem representative_all {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v) (P Q : CochainComplex (modules Λ Y) ℤ) :
    letI := derivedMonoidal Λ X
    μ.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        ((pullback Λ f).mapDerivedCategoryFactors.hom.app P ⊗ₘ
          (pullback Λ f).mapDerivedCategoryFactors.hom.app Q) ≫
        modelTensor Λ X ((totalSectionPull Λ f).obj P) ((totalSectionPull Λ f).obj Q) =
      (derivedPullback Λ f).map (modelTensor Λ Y P Q) ≫
        (pullback Λ f).mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (sectionTotalIso Λ f P Q).hom := by
  let := derivedMonoidal Λ Y
  let := derivedMonoidal Λ X
  apply representative_extension (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q (modelTensor Λ Y) (modelTensor Λ X)
    (pullback Λ f).mapDerivedCategoryFactors.hom
    (fun A B ↦ (sectionTotalIso Λ f A B).hom) μ
    (R := fun A ↦ KFlatSectionComparison.sectionResolving Λ Y A)
  · intro A A' B B' a b
    simpa only [qTensorArrow, Functor.prod_obj, totalTensor_obj_tensor,
      modelTensor, section_tensor_map] using
      qTensorArrow_naturality Λ X a b
  · intro A A' B B' a b
    simpa only [qTensorArrow, Functor.prod_obj, totalTensor_obj_tensor,
      modelTensor, section_tensor_map] using
      qTensorArrow_naturality Λ Y a b
  · intro A A' B B' a b
    simpa only [sectionTotalIso_δ] using
      (Functor.OplaxMonoidal.δ_natural (totalSectionPull Λ f) a b).symm
  · intro P
    obtain ⟨R, r, hR, hr⟩ := section_resolution Λ Y P
    have := hr
    exact ⟨R, r, hR, inferInstance⟩
  · intro A B hA hB
    simpa only [pairModel, Category.assoc] using h.1 ⟨A, hA⟩ ⟨B, hB⟩

/--
Under the representative equations, the six prescribed edge squares commute
for every triple of resolving section complexes.  The proof expands the fixed
vertices, uses naturality of the resolution comparison and of `modelTensor`,
and applies the representative equation to the relevant binary pair; the
source and target associator equations identify the remaining edge.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E.
(auxiliary; not a blueprint node).
-/
theorem section_resolving_oplax_edge_identifications {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v)
    (P Q H : CochainComplex (modules Λ Y) ℤ) :
    SectionEdges Λ f μ P Q H := by
  let := derivedMonoidal Λ Y
  let := derivedMonoidal Λ X
  apply edge_calculus (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q (modelTensor Λ Y) (modelTensor Λ X)
    (pullback Λ f).mapDerivedCategoryFactors.hom
    (fun A B ↦ (sectionTotalIso Λ f A B).hom) μ
  · exact representative_all Λ f μ v h
  · exact section_localization_associativity Λ Y
  · exact section_localization_associativity Λ X
  · intro A A' B B' a b
    simpa only [qTensorArrow, Functor.prod_obj, Functor.comp_obj, totalTensor_obj_tensor,
    modelTensor, section_tensor_map] using
      qTensorArrow_naturality Λ X a b

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
