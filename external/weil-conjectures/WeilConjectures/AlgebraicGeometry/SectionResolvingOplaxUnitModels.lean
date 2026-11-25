/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.AlgebraicGeometry.SectionLocalizationUnitConstraints
import WeilConjectures.AlgebraicGeometry.SectionRepresentativeTensorArrow

/-! # Resolving regular-unit diagrams

Source: Stacks Project, Tags 07A4 and 0G7E; the corresponding explicit
representative calculation of the resolving constraint diagram.
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

section UnitCalculus
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
  (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q))
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
  (unit : F.obj (𝟙_ A) ⟶ 𝟙_ B)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (μ : ∀ M N : C, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B))

private theorem regularLeft_natural {M N : C} (g : M ⟶ N) :
    (q.obj (𝟙_ A) ◁ g) ≫ regularLeft q eA N = regularLeft q eA M ≫ g := by
  simp only [regularLeft, Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality]

private theorem regularRight_natural {M N : C} (g : M ⟶ N) :
    (g ▷ q.obj (𝟙_ A)) ≫ regularRight q eA N = regularRight q eA M ≫ g := by
  simp only [regularRight, Category.assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

private theorem unit_edges (P : A)
    [IsIso (s (𝟙_ A) P)] [IsIso (s P (𝟙_ A))]
    [∀ Z, IsIso (ε.app Z)] [IsIso unit]
    (hl : μ (q.obj (𝟙_ A)) (q.obj P) ≫
      (ε.app (𝟙_ A) ⊗ₘ ε.app P) ≫ t (F.obj (𝟙_ A)) (F.obj P) =
      pairModel F L q r s ε (𝟙_ A) P ≫ r.map (β (𝟙_ A) P))
    (hr : μ (q.obj P) (q.obj (𝟙_ A)) ≫
      (ε.app P ⊗ₘ ε.app (𝟙_ A)) ≫ t (F.obj P) (F.obj (𝟙_ A)) =
      pairModel F L q r s ε P (𝟙_ A) ≫ r.map (β P (𝟙_ A)))
    (hv : v = ε.app (𝟙_ A) ≫ r.map unit)
    (hnl : (r.map unit ⊗ₘ 𝟙 (r.obj (F.obj P))) ≫ t (𝟙_ B) (F.obj P) =
      t (F.obj (𝟙_ A)) (F.obj P) ≫ r.map (unit ▷ F.obj P))
    (hnr : (𝟙 (r.obj (F.obj P)) ⊗ₘ r.map unit) ≫ t (F.obj P) (𝟙_ B) =
      t (F.obj P) (F.obj (𝟙_ A)) ≫ r.map (F.obj P ◁ unit))
    (hsl : s (𝟙_ A) P ≫ q.map (λ_ P).hom = regularLeft q eA (q.obj P))
    (hsr : s P (𝟙_ A) ≫ q.map (ρ_ P).hom = regularRight q eA (q.obj P))
    (htl : t (𝟙_ B) (F.obj P) ≫ r.map (λ_ (F.obj P)).hom =
      regularLeft r eB (r.obj (F.obj P)))
    (htr : t (F.obj P) (𝟙_ B) ≫ r.map (ρ_ (F.obj P)).hom =
      regularRight r eB (r.obj (F.obj P))) :
    UnitEdgeIdentification F L q r s t ε β unit eA eB μ v P := by
  have h12 : (v ▷ L.obj (q.obj P)) ≫ leftVertex2 F L q r t ε P =
      leftVertex1 F L q r t ε P ≫ r.map (unit ▷ F.obj P) := by
    dsimp only [leftVertex1, leftVertex2]
    rw [hv, ← tensorHom_id]
    have he : ((ε.app (𝟙_ A) ≫ r.map unit) ⊗ₘ 𝟙 (L.obj (q.obj P))) ≫
        (𝟙 (r.obj (𝟙_ B)) ⊗ₘ ε.app P) =
        (ε.app (𝟙_ A) ⊗ₘ ε.app P) ≫ (r.map unit ⊗ₘ 𝟙 (r.obj (F.obj P))) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1 <;> simp only [Functor.comp_obj, Category.comp_id, Category.id_comp]
    rw [← Category.assoc, he, Category.assoc, hnl, Category.assoc]
  have k12 : (L.obj (q.obj P) ◁ v) ≫ rightVertex2 F L q r t ε P =
      rightVertex1 F L q r t ε P ≫ r.map (F.obj P ◁ unit) := by
    dsimp only [rightVertex1, rightVertex2]
    rw [hv, ← id_tensorHom]
    have he : (𝟙 (L.obj (q.obj P)) ⊗ₘ (ε.app (𝟙_ A) ≫ r.map unit)) ≫
        (ε.app P ⊗ₘ 𝟙 (r.obj (𝟙_ B))) =
        (ε.app P ⊗ₘ ε.app (𝟙_ A)) ≫ (𝟙 (r.obj (F.obj P)) ⊗ₘ r.map unit) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      congr 1 <;> simp only [Functor.comp_obj, Category.comp_id, Category.id_comp]
    rw [← Category.assoc, he, Category.assoc, hnr, Category.assoc]
  have h23 : regularLeft r eB (L.obj (q.obj P)) ≫ ε.app P =
      leftVertex2 F L q r t ε P ≫ r.map (λ_ (F.obj P)).hom := by
    dsimp only [leftVertex2]
    rw [Category.assoc, htl, id_tensorHom]
    exact (regularLeft_natural r eB (ε.app P)).symm
  have k23 : regularRight r eB (L.obj (q.obj P)) ≫ ε.app P =
      rightVertex2 F L q r t ε P ≫ r.map (ρ_ (F.obj P)).hom := by
    dsimp only [rightVertex2]
    rw [Category.assoc, htr, tensorHom_id]
    exact (regularRight_natural r eB (ε.app P)).symm
  have h03 : L.map (regularLeft q eA (q.obj P)) ≫ ε.app P =
      pairModel F L q r s ε (𝟙_ A) P ≫ r.map (F.map (λ_ P).hom) := by
    rw [← hsl, Functor.map_comp, Category.assoc]
    simpa only [pairModel, Category.assoc, Functor.comp_map] using
      congrArg (L.map (s (𝟙_ A) P) ≫ ·) (ε.naturality (λ_ P).hom)
  have k03 : L.map (regularRight q eA (q.obj P)) ≫ ε.app P =
      pairModel F L q r s ε P (𝟙_ A) ≫ r.map (F.map (ρ_ P).hom) := by
    rw [← hsr, Functor.map_comp, Category.assoc]
    simpa only [pairModel, Category.assoc, Functor.comp_map] using
      congrArg (L.map (s P (𝟙_ A)) ≫ ·) (ε.naturality (ρ_ P).hom)
  have : IsIso (leftVertex2 F L q r t ε P ≫ r.map (λ_ (F.obj P)).hom) := by
    rw [← h23]; dsimp only [regularLeft]; infer_instance
  have : IsIso (leftVertex2 F L q r t ε P) :=
    IsIso.of_isIso_comp_right _ (r.map (λ_ (F.obj P)).hom)
  have : IsIso v := by rw [hv]; infer_instance
  have : IsIso (leftVertex1 F L q r t ε P ≫ r.map (unit ▷ F.obj P)) := by
    rw [← h12]; infer_instance
  have : IsIso (leftVertex1 F L q r t ε P) :=
    IsIso.of_isIso_comp_right _ (r.map (unit ▷ F.obj P))
  have : IsIso (rightVertex2 F L q r t ε P ≫ r.map (ρ_ (F.obj P)).hom) := by
    rw [← k23]; dsimp only [regularRight]; infer_instance
  have : IsIso (rightVertex2 F L q r t ε P) :=
    IsIso.of_isIso_comp_right _ (r.map (ρ_ (F.obj P)).hom)
  have : IsIso (rightVertex1 F L q r t ε P ≫ r.map (F.obj P ◁ unit)) := by
    rw [← k12]; infer_instance
  have : IsIso (rightVertex1 F L q r t ε P) :=
    IsIso.of_isIso_comp_right _ (r.map (F.obj P ◁ unit))
  -- The resolution comparison is an isomorphism at tensor products as well.
  have hi0 : IsIso (pairModel F L q r s ε (𝟙_ A) P) := by
    dsimp only [pairModel]
    infer_instance
  have hj0 : IsIso (pairModel F L q r s ε P (𝟙_ A)) := by
    dsimp only [pairModel]
    infer_instance
  exact ⟨hi0, inferInstance, inferInstance, inferInstance, hl, h12, h23, h03,
    hj0, inferInstance, inferInstance, inferInstance, hr, k12, k23, k03⟩
end UnitCalculus

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] qTensor tensorComparison totalComparison

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem section_unit_resolving (T : Scheme.{u}) :
    KFlatSectionComparison.sectionResolving Λ T
      (𝟙_ (CochainComplex (modules Λ T) ℤ)) := by
  refine ⟨?_, ?_⟩
  · intro F hF
    exact fun i ↦ (hF i).of_iso (HomologicalComplex.rightUnitor F).symm
  · intro n
    apply (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ring Λ T)
        ((𝟙_ (CochainComplex (modules Λ T) ℤ)).X n)).symm
    by_cases hn : n = 0
    · subst n
      have hu : exactFunctor (modules Λ T) (modules Λ T)
          (tensorRight (𝟙_ (modules Λ T))) :=
        ⟨preservesFiniteLimits_of_natIso (rightUnitorNatIso _).symm,
          preservesFiniteColimits_of_natIso (rightUnitorNatIso _).symm⟩
      exact (exactFunctor _ _).prop_of_iso
        ((curriedTensor (modules Λ T)).flip.mapIso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (modules Λ T))).symm) hu
    · let G := tensorRight ((𝟙_ (CochainComplex (modules Λ T) ℤ)).X n)
      have hz : IsZero G := G.isZero (fun M ↦
        (tensorLeft M).map_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ (modules Λ T)) n hn))
      let := G.preservesLimitsOfSize_of_isZero hz
      let := G.preservesColimitsOfSize_of_isZero hz
      change PreservesFiniteLimits G ∧ PreservesFiniteColimits G
      exact ⟨inferInstance, inferInstance⟩

private theorem section_tensor_map (T : Scheme.{u})
    {M M' N N' : DerivedCategory (modules Λ T)} (a : M ⟶ M') (b : N ⟶ N') :
    (tensor Λ T).map (Prod.mkHom a b) =
      @MonoidalCategoryStruct.tensorHom _ _ (derivedMonoidal Λ T).toMonoidalCategoryStruct
        M M' N N' a b := by
  rfl

/-- The prescribed regular-unit models identify both unit diagrams.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4; Steps 9–10 of
lem-pd-section-resolving-oplax-constraint-diagrams.

Proof: the degree-zero regular module is resolving and so is its pullback. Its
binary model maps, all resolution counits, and their tensor products are therefore
invertible, giving the eight invertibility clauses. For the first left edge use
the representative equation at the regular unit and P. For the second substitute
v = ε at the unit followed by the localized scalar-unit arrow, and use naturality
of the target modelTensor. For the third use naturality of the left unitor in ε_P
and the normalized target modelTensor unitor equation. Composing these three
squares is postponed to the consumer. Naturality of ε and the source
modelTensor unitor equation give the opposite branch. Repeat with tensor factors
reversed and the right unitor to obtain every right-unit edge clause. In both cases
retain the specified scalar unit, regular comparison and binary model map throughout.
(auxiliary; not a blueprint node). -/
theorem section_resolving_oplax_unit_models {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v) :
    ∀ P : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
      SectionUnitEdges Λ f μ v P.obj := by
  let := derivedMonoidal Λ Y
  let := derivedMonoidal Λ X
  intro P
  let U : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory :=
    ⟨𝟙_ _, section_unit_resolving Λ Y⟩
  have hY (A B : CochainComplex (modules Λ Y) ℤ)
      (hAB : A.IsKFlatIndependentCoefficients ∨ B.IsKFlatIndependentCoefficients) :
      IsIso (modelTensor Λ Y A B) := by
    simpa only [modelTensor, qTensor] using
      (tensor_representatives Λ Y).exists.choose_spec.2.1 A B hAB
  have := hY (𝟙_ _) P.obj (Or.inr P.property.1)
  have := hY P.obj (𝟙_ _) (Or.inl P.property.1)
  have : IsIso (sectionTotalUnit Λ f) := by
    rw [sectionTotalUnit_η]
    infer_instance
  apply unit_edges (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q (modelTensor Λ Y) (modelTensor Λ X)
    (pullback Λ f).mapDerivedCategoryFactors.hom
    (fun A B ↦ (sectionTotalIso Λ f A B).hom) (sectionTotalUnit Λ f)
    (regular Λ Y) (regular Λ X) (fun M N ↦ μ.app (M, N)) v P.obj
  · exact h.1 U P
  · exact h.1 P U
  · exact h.2
  · have hn := qTensorArrow_naturality Λ X (sectionTotalUnit Λ f)
        (𝟙 ((totalSectionPull Λ f).obj P.obj))
    simpa only [qTensorArrow, modelTensor, section_tensor_map,
      CategoryTheory.Functor.map_id, tensorHom_id, sectionCochainUnit] using hn
  · have hn := qTensorArrow_naturality Λ X (𝟙 ((totalSectionPull Λ f).obj P.obj))
        (sectionTotalUnit Λ f)
    simpa only [qTensorArrow, modelTensor, section_tensor_map,
      CategoryTheory.Functor.map_id, id_tensorHom, sectionCochainUnit] using hn
  · exact (section_localization_unit_constraints Λ Y P.obj).1
  · exact (section_localization_unit_constraints Λ Y P.obj).2
  · exact (section_localization_unit_constraints Λ X ((totalSectionPull Λ f).obj P.obj)).1
  · exact (section_localization_unit_constraints Λ X ((totalSectionPull Λ f).obj P.obj)).2

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
