/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxUnitModels
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Internal conjugation of constraint diagrams

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

section GenericEdges
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  [q.LaxMonoidal] [r.LaxMonoidal]
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
  (μ : MonoidalCategory.tensor C ⋙ L ⟶
    L.prod L ⋙ MonoidalCategory.tensor D)
  (hp : ∀ P Q, μ.app (q.obj P, q.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫
    Functor.LaxMonoidal.μ r (F.obj P) (F.obj Q) =
      L.map (Functor.LaxMonoidal.μ q P Q) ≫ ε.app (P ⊗ Q) ≫ r.map (β P Q))

include hp in
private theorem generic_edges (P Q H : A) :
    EdgeIdentification F L q r (Functor.LaxMonoidal.μ q) (Functor.LaxMonoidal.μ r)
      ε β (fun M N ↦ μ.app (M, N)) P Q H := by
  dsimp only [EdgeIdentification, vertex0, vertex1, vertex2, vertex3,
    vertex4, vertex5, leftModel, rightModel, pairModel, Functor.comp_obj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tensorHom_id, id_tensorHom, Functor.map_comp, Category.assoc]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc (α_ (q.obj P) (q.obj Q) (q.obj H)).hom,
      ← Functor.LaxMonoidal.associativity, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc]
    erw [ε.naturality (α_ P Q H).hom]
    rfl
  · have hn := μ.naturality (Prod.mkHom (𝟙 (q.obj P))
      (Functor.LaxMonoidal.μ q Q H))
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
    erw [Functor.LaxMonoidal.μ_natural_right r (F.obj P) (β Q H)]
    erw [whiskerLeft_comp_tensorHom_assoc]
  · have hn := μ.naturality (Prod.mkHom (Functor.LaxMonoidal.μ q P Q)
      (𝟙 (q.obj H)))
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
    erw [Functor.LaxMonoidal.μ_natural_left r (β P Q) (F.obj H)]
    erw [whiskerRight_comp_tensorHom_assoc]
  · simp only [id_tensorHom, tensorHom_id, Category.assoc]
    erw [← associator_naturality_assoc, Functor.LaxMonoidal.associativity]

end GenericEdges

section GenericUnits
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]

private theorem regular_left_eq (q : A ⥤ C) [q.LaxMonoidal]
    (e : 𝟙_ C ≅ q.obj (𝟙_ A)) (he : e.hom = Functor.LaxMonoidal.ε q) (P : A) :
    regularLeft q e (q.obj P) =
      Functor.LaxMonoidal.μ q (𝟙_ A) P ≫ q.map (λ_ P).hom := by
  unfold regularLeft
  rw [Functor.LaxMonoidal.left_unitality q, ← he]
  simp only [← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp]

private theorem regular_right_eq (q : A ⥤ C) [q.LaxMonoidal]
    (e : 𝟙_ C ≅ q.obj (𝟙_ A)) (he : e.hom = Functor.LaxMonoidal.ε q) (P : A) :
    regularRight q e (q.obj P) =
      Functor.LaxMonoidal.μ q P (𝟙_ A) ≫ q.map (ρ_ P).hom := by
  unfold regularRight
  rw [Functor.LaxMonoidal.right_unitality q, ← he]
  simp only [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    whiskerLeft_id, Category.id_comp]

variable (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  [q.Monoidal] [r.Monoidal]
  (ε : q ⋙ L ⟶ F ⋙ r) [IsIso ε]
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
  (unit : F.obj (𝟙_ A) ⟶ 𝟙_ B)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (heA : eA.hom = Functor.LaxMonoidal.ε q)
  (heB : eB.hom = Functor.LaxMonoidal.ε r)
  (μ : ∀ M N : C, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B))
  (hp : ∀ P Q, μ (q.obj P) (q.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫
    Functor.LaxMonoidal.μ r (F.obj P) (F.obj Q) =
      L.map (Functor.LaxMonoidal.μ q P Q) ≫ ε.app (P ⊗ Q) ≫ r.map (β P Q))
  (hv : v = ε.app (𝟙_ A) ≫ r.map unit)

include hp hv heA heB in
private theorem generic_unit_edges (P : A) :
    UnitEdgeIdentification F L q r (Functor.LaxMonoidal.μ q) (Functor.LaxMonoidal.μ r)
      ε β unit eA eB μ v P := by
  have hl (M : C) (a : L.obj M ⟶ r.obj (F.obj P)) :
      regularLeft r eB (L.obj M) ≫ a =
        (r.obj (𝟙_ B) ◁ a) ≫ regularLeft r eB (r.obj (F.obj P)) := by
    simp only [regularLeft, Category.assoc, leftUnitor_naturality,
      whisker_exchange_assoc]
  have hr (M : C) (a : L.obj M ⟶ r.obj (F.obj P)) :
      regularRight r eB (L.obj M) ≫ a =
        (a ▷ r.obj (𝟙_ B)) ≫ regularRight r eB (r.obj (F.obj P)) := by
    simp only [regularRight, Category.assoc, rightUnitor_naturality,
      ← whisker_exchange_assoc]
  dsimp only [UnitEdgeIdentification, pairModel, leftVertex1, leftVertex2,
    rightVertex1, rightVertex2, Functor.comp_obj]
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    (by simpa only [Category.assoc] using hp (𝟙_ A) P), ?_, ?_, ?_,
    inferInstance, inferInstance, inferInstance, inferInstance,
    (by simpa only [Category.assoc] using hp P (𝟙_ A)), ?_, ?_, ?_⟩
  · erw [whiskerRight_comp_tensorHom_assoc]
    simp only [Category.comp_id, hv]
    erw [← tensorHom_comp_whiskerRight (ε.app (𝟙_ A))
      (r.map unit) (ε.app P), Category.assoc,
      Functor.LaxMonoidal.μ_natural_left r unit (F.obj P)]
    simp only [Category.assoc]
  · rw [hl, regular_left_eq r eB heB]
    simp only [id_tensorHom, Category.assoc]
  · rw [regular_left_eq q eA heA, Functor.map_comp, Category.assoc]
    erw [ε.naturality (λ_ P).hom]
    simp only [Functor.comp_map, Category.assoc]
  · erw [whiskerLeft_comp_tensorHom_assoc]
    simp only [Category.comp_id, hv]
    erw [← tensorHom_comp_whiskerLeft (ε.app P)
      (ε.app (𝟙_ A)) (r.map unit), Category.assoc,
      Functor.LaxMonoidal.μ_natural_right r (F.obj P) unit]
    simp only [Category.assoc]
  · rw [hr, regular_right_eq r eB heB]
    simp only [tensorHom_id, Category.assoc]
  · rw [regular_right_eq q eA heA, Functor.map_comp, Category.assoc]
    erw [ε.naturality (ρ_ P).hom]
    simp only [Functor.comp_map, Category.assoc]

omit [q.Monoidal] [r.Monoidal] [IsIso ε] in
private theorem unit_laws_from_edges
    (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
    (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q)) (P : A)
    (h : UnitEdgeIdentification F L q r s t ε β unit eA eB μ v P)
    (hl : β (𝟙_ A) P ≫ unit ▷ F.obj P ≫ (λ_ (F.obj P)).hom = F.map (λ_ P).hom)
    (hr : β P (𝟙_ A) ≫ F.obj P ◁ unit ≫ (ρ_ (F.obj P)).hom = F.map (ρ_ P).hom) :
    leftUnitPath L q r eB μ v (q.obj P) = L.map (regularLeft q eA (q.obj P)) ∧
      rightUnitPath L q r eB μ v (q.obj P) = L.map (regularRight q eA (q.obj P)) := by
  rcases h with ⟨_, _, _, hi, h01, h12, h23, h03,
    _, _, _, _, k01, k12, k23, k03⟩
  have : IsIso (ε.app P) := hi
  constructor
  · apply (cancel_mono (ε.app P)).1
    simp only [leftUnitPath, Category.assoc, h23, reassoc_of% h12,
      reassoc_of% h01, ← r.map_comp, hl]
    exact h03.symm
  · apply (cancel_mono (ε.app P)).1
    simp only [rightUnitPath, Category.assoc, k23, reassoc_of% k12,
      reassoc_of% k01, ← r.map_comp, hr]
    exact k03.symm

omit [q.Monoidal] [r.Monoidal] [IsIso ε] in
private theorem units_from_edges_and_laws
    (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
    (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q)) (P : A)
    (h : UnitEdgeIdentification F L q r s t ε β unit eA eB μ v P)
    (hl : leftUnitPath L q r eB μ v (q.obj P) = L.map (regularLeft q eA (q.obj P)))
    (hr : rightUnitPath L q r eB μ v (q.obj P) = L.map (regularRight q eA (q.obj P))) :
    UnitIdentification F L q r s t ε β unit eA eB μ v P := by
  rcases h with ⟨hi0, hi1, hi2, hi3, h01, h12, h23, h03,
    hj0, hj1, hj2, hj3, k01, k12, k23, k03⟩
  refine ⟨hi0, hi1, hi2, hi3, h01, h12, h23, ?_, h03, hl,
    hj0, hj1, hj2, hj3, k01, k12, k23, ?_, k03, hr⟩
  · simp only [leftUnitPath, Functor.map_comp, Category.assoc,
      h23, reassoc_of% h12, reassoc_of% h01]
  · simp only [rightUnitPath, Functor.map_comp, Category.assoc,
      k23, reassoc_of% k12, reassoc_of% k01]

end GenericUnits

section NormalizedUnits
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (μ : MonoidalCategory.tensor C ⋙ L ⟶
    L.prod L ⋙ MonoidalCategory.tensor D)
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B))

private def curry_tensor_arrow :
    (Functor.postcompose₂.obj L).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj (curriedTensor D) where
  app M :=
    { app N := μ.app (M, N)
      naturality N N' a := by
        have hn := μ.naturality (Prod.mkHom (𝟙 M) a)
        dsimp at hn
        simp only [L.map_id, id_tensorHom] at hn
        exact hn }
  naturality M M' a := by
    ext N
    have hn := μ.naturality (Prod.mkHom a (𝟙 N))
    dsimp at hn
    simp only [L.map_id, tensorHom_id] at hn
    exact hn

private theorem left_normalized_iff (M : C) :
    leftUnitPath L q r eB (fun M N ↦ μ.app (M, N)) v M =
        L.map (regularLeft q eA M) ↔
      μ.app (𝟙_ C, M) ≫ (L.map eA.hom ≫ v ≫ eB.inv) ▷ L.obj M ≫
        (λ_ (L.obj M)).hom = L.map (λ_ M).hom := by
  have hn := μ.naturality (Prod.mkHom eA.hom (𝟙 M))
  dsimp at hn
  simp only [L.map_id, tensorHom_id] at hn
  simp only [leftUnitPath, regularLeft, Functor.map_comp, comp_whiskerRight,
    Category.assoc]
  erw [← reassoc_of% hn]
  constructor
  · intro h
    erw [h]
    simp only [← L.map_comp_assoc, ← comp_whiskerRight, Iso.hom_inv_id,
      id_whiskerRight, L.map_id, Category.id_comp]
  · intro h
    apply (cancel_epi (L.map (eA.hom ▷ M))).1
    erw [h]
    simp only [← L.map_comp_assoc, ← comp_whiskerRight, Iso.hom_inv_id,
      id_whiskerRight, L.map_id, Category.id_comp]

private theorem right_normalized_iff (M : C) :
    rightUnitPath L q r eB (fun M N ↦ μ.app (M, N)) v M =
        L.map (regularRight q eA M) ↔
      μ.app (M, 𝟙_ C) ≫ L.obj M ◁ (L.map eA.hom ≫ v ≫ eB.inv) ≫
        (ρ_ (L.obj M)).hom = L.map (ρ_ M).hom := by
  have hn := μ.naturality (Prod.mkHom (𝟙 M) eA.hom)
  dsimp at hn
  simp only [L.map_id, id_tensorHom] at hn
  simp only [rightUnitPath, regularRight, Functor.map_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  erw [← reassoc_of% hn]
  constructor
  · intro h
    erw [h]
    simp only [← L.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, L.map_id, Category.id_comp]
  · intro h
    apply (cancel_epi (L.map (M ◁ eA.hom))).1
    erw [h]
    simp only [← L.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, L.map_id, Category.id_comp]

end NormalizedUnits

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] tensorComparison qTensor totalComparison

private theorem internal_monoidal (T : Scheme.{u}) :
    ∃ l : @Functor.Monoidal (DerivedCategory (internalModules Λ T)) _ _
        (DerivedCategory (modules Λ T)) _ (derivedMonoidal Λ T)
        (derivedEquivalence Λ T).functor,
      l.toLaxMonoidal.ε = 𝟙 _ ∧
      ∀ M N, l.toLaxMonoidal.μ M N = internalModelTensor Λ T M N := by
  obtain ⟨_, _, hc⟩ :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 1, u + 1} Λ T).2.2.2.2.2.2.2.2
  have hc' : ∃ o : @Functor.OplaxMonoidal
      (DerivedCategory (internalModules Λ T)) _ _
      (DerivedCategory (modules Λ T)) _ (derivedMonoidal Λ T)
      (derivedEquivalence Λ T).functor,
      o.η = 𝟙 _ ∧ ∀ M N, o.δ M N = (tensorComparison Λ T).hom.app (M, N) := by
    simpa only [KFlatSectionComparison.ConstraintCondition,
      derivedMonoidal, transportedDerivedMonoidal,
      TensorFunctorTransport.monoidal_eq] using hc
  obtain ⟨o, ho, ht⟩ := hc'
  let := derivedMonoidal Λ T
  let := o
  have : IsIso (Functor.OplaxMonoidal.η (derivedEquivalence Λ T).functor) := by
    change IsIso o.η
    rw [ho]
    infer_instance
  have (M N : DerivedCategory (internalModules Λ T)) :
      IsIso (Functor.OplaxMonoidal.δ (derivedEquivalence Λ T).functor M N) := by
    change IsIso (o.δ M N)
    rw [ht]
    infer_instance
  let l := Functor.Monoidal.ofOplaxMonoidal (derivedEquivalence Λ T).functor
  refine ⟨l, ?_, ?_⟩
  · change inv o.η = 𝟙 _
    simp only [ho, IsIso.inv_id]
    rfl
  · intro M N
    change inv (o.δ M N) = internalModelTensor Λ T M N
    simp only [ht, internalModelTensor, NatIso.inv_hom_app]

private theorem section_unit_laws {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v) :
    letI := derivedMonoidal Λ Y
    letI := derivedMonoidal Λ X
    let η := (derivedPullback Λ f).map (regular Λ Y).hom ≫ v ≫ (regular Λ X).inv
    (∀ M, μ.app (𝟙_ _, M) ≫ η ▷ (derivedPullback Λ f).obj M ≫
      (λ_ ((derivedPullback Λ f).obj M)).hom = (derivedPullback Λ f).map (λ_ M).hom) ∧
    (∀ M, μ.app (M, 𝟙_ _) ≫ (derivedPullback Λ f).obj M ◁ η ≫
      (ρ_ ((derivedPullback Λ f).obj M)).hom = (derivedPullback Λ f).map (ρ_ M).hom) := by
  let := derivedMonoidal Λ Y
  let := derivedMonoidal Λ X
  let L := derivedPullback Λ f
  let η := L.map (regular Λ Y).hom ≫ v ≫ (regular Λ X).inv
  let μc := curry_tensor_arrow L μ
  have hmodels (P : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory) :
      leftUnitPath L DerivedCategory.Q DerivedCategory.Q (regular Λ X)
        (fun M N ↦ μ.app (M, N)) v (DerivedCategory.Q.obj P.obj) =
          L.map (regularLeft DerivedCategory.Q (regular Λ Y)
            (DerivedCategory.Q.obj P.obj)) ∧
      rightUnitPath L DerivedCategory.Q DerivedCategory.Q (regular Λ X)
        (fun M N ↦ μ.app (M, N)) v (DerivedCategory.Q.obj P.obj) =
          L.map (regularRight DerivedCategory.Q (regular Λ Y)
            (DerivedCategory.Q.obj P.obj)) := by
    apply unit_laws_from_edges (totalSectionPull Λ f) L
      DerivedCategory.Q DerivedCategory.Q
      (pullback Λ f).mapDerivedCategoryFactors.hom
      (fun P Q ↦ (sectionTotalIso Λ f P Q).hom) (sectionTotalUnit Λ f)
      (regular Λ Y) (regular Λ X) (fun M N ↦ μ.app (M, N)) v
      (modelTensor Λ Y) (modelTensor Λ X) P.obj
      (section_resolving_oplax_unit_models Λ f μ v h P)
    · exact (section_oplax_total_comparison Λ f).2.2.2.2.2.2.2.2.2.2.1 P.obj |>.1
    · exact (section_oplax_total_comparison Λ f).2.2.2.2.2.2.2.2.2.2.2 P.obj |>.1
  have hrep (M : DerivedCategory (modules Λ Y)) :
      ∃ P : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
        Nonempty (DerivedCategory.Q.obj P.obj ≅ M) := by
    obtain ⟨P, a, hP, hf, ha, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (DerivedCategory.Q.objPreimage M)
    have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology Y)
        (R := ring Λ Y) (P.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (ring Λ Y) (P.X n)).symm (hf n)
    have := ha
    exact ⟨⟨P, hP, hflat⟩,
      ⟨asIso (DerivedCategory.Q.map a) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩
  constructor
  · intro M
    obtain ⟨P, ⟨i⟩⟩ := hrep M
    have hl := (left_normalized_iff L DerivedCategory.Q DerivedCategory.Q
      (regular Λ Y) (regular Λ X) μ v _).mp (hmodels P).1
    have hi : (λ_ (L.obj (DerivedCategory.Q.obj P.obj))).inv =
        L.map (λ_ (DerivedCategory.Q.obj P.obj)).inv ≫
          μ.app (𝟙_ _, DerivedCategory.Q.obj P.obj) ≫ η ▷ L.obj
            (DerivedCategory.Q.obj P.obj) := by
      apply (cancel_mono (λ_ (L.obj (DerivedCategory.Q.obj P.obj))).hom).1
      simp only [Category.assoc, Iso.inv_hom_id]
      rw [hl, ← L.map_comp, Iso.inv_hom_id, L.map_id]
    have hg := Functor.OplaxMonoidal.oplax_left_unitality_of_iso μc i hi
    change (λ_ (L.obj M)).inv = L.map (λ_ M).inv ≫
      μ.app (𝟙_ _, M) ≫ η ▷ L.obj M at hg
    change μ.app (𝟙_ _, M) ≫ η ▷ L.obj M ≫ (λ_ (L.obj M)).hom =
      L.map (λ_ M).hom
    apply (cancel_epi (L.map (λ_ M).inv)).1
    calc
      _ = (L.map (λ_ M).inv ≫ μ.app (𝟙_ _, M) ≫ η ▷ L.obj M) ≫
          (λ_ (L.obj M)).hom := by simp only [Category.assoc]
      _ = (λ_ (L.obj M)).inv ≫ (λ_ (L.obj M)).hom := by erw [← hg]
      _ = _ := by simp only [Iso.inv_hom_id, ← L.map_comp, L.map_id]
  · intro M
    obtain ⟨P, ⟨i⟩⟩ := hrep M
    have hr := (right_normalized_iff L DerivedCategory.Q DerivedCategory.Q
      (regular Λ Y) (regular Λ X) μ v _).mp (hmodels P).2
    have hi : (ρ_ (L.obj (DerivedCategory.Q.obj P.obj))).inv =
        L.map (ρ_ (DerivedCategory.Q.obj P.obj)).inv ≫
          μ.app (DerivedCategory.Q.obj P.obj, 𝟙_ _) ≫
            L.obj (DerivedCategory.Q.obj P.obj) ◁ η := by
      apply (cancel_mono (ρ_ (L.obj (DerivedCategory.Q.obj P.obj))).hom).1
      simp only [Category.assoc, Iso.inv_hom_id]
      rw [hr, ← L.map_comp, Iso.inv_hom_id, L.map_id]
    have hg := Functor.OplaxMonoidal.oplax_right_unitality_of_iso μc i hi
    change (ρ_ (L.obj M)).inv = L.map (ρ_ M).inv ≫
      μ.app (M, 𝟙_ _) ≫ L.obj M ◁ η at hg
    change μ.app (M, 𝟙_ _) ≫ L.obj M ◁ η ≫ (ρ_ (L.obj M)).hom =
      L.map (ρ_ M).hom
    apply (cancel_epi (L.map (ρ_ M).inv)).1
    calc
      _ = (L.map (ρ_ M).inv ≫ μ.app (M, 𝟙_ _) ≫ L.obj M ◁ η) ≫
          (ρ_ (L.obj M)).hom := by simp only [Category.assoc]
      _ = (ρ_ (L.obj M)).inv ≫ (ρ_ (L.obj M)).hom := by erw [← hg]
      _ = _ := by simp only [Iso.inv_hom_id, ← L.map_comp, L.map_id]

/-- Conjugation identifies the internal edges and units with the fixed section models.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4; Steps 11–12 of
lem-pd-section-resolving-oplax-constraint-diagrams, with the fixed tensor and derived
pullback normalization theorems.

Proof: expand Conjugation as its pair and unit equations. At each associativity
vertex use the nested inverse tensor comparisons and the inverse derived pullback
comparison prescribed by vertex0 through vertex5. Naturality of μ moves each
source tensor comparison past a splitting edge. Substitute the pair equation;
then naturality of the derived pullback comparison moves it past the internal
splitting arrow. Adjacent comparison/inverse factors cancel. For inner edges use
bifunctoriality and naturality of the target tensor comparison. For the source
and target associator edges use the normalized associator equations for the fixed
tensor comparisons. These are precisely the six InternalEdges clauses. At unit
vertices replace the corresponding tensor factor by the transported unit identity;
the unit conjugation equation and the two normalized unitor equations give the
three edge squares and the opposite branch for each unit. All vertex maps are
composites of isomorphisms. Compose the edge squares and cancel the common final
vertex map to obtain the whole paths and their equalities; the section unit laws
hold on all objects by resolving localization and the given representative
hypotheses. The resolution compatibility of the derived pullback comparison and
the tensor representative normalization identify these vertex maps on resolving
objects with the same nested modelTensor and ε maps, so no replacement endpoint
comparison is introduced.
(auxiliary; not a blueprint node). -/
theorem section_resolving_oplax_internal_conjugation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (μ : SectionTensorArrow Λ f)
    (v : (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
        DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)))
    (h : SectionHypotheses Λ f μ v) :
    ∀ (δ : InternalTensorArrow Λ f)
      (w : (internalDerivedPullback Λ f).obj
          (𝟙_ (DerivedCategory (internalModules Λ Y))) ⟶
        𝟙_ (DerivedCategory (internalModules Λ X))),
      Conjugation Λ f μ v δ w →
        (∀ M N H : DerivedCategory (internalModules Λ Y), InternalEdges Λ f μ δ M N H) ∧
        (∀ M : DerivedCategory (internalModules Λ Y), InternalUnits Λ f μ v δ w M) := by
  let := derivedMonoidal Λ Y
  let := derivedMonoidal Λ X
  obtain ⟨lY, hεY, hμY⟩ := internal_monoidal Λ Y
  obtain ⟨lX, hεX, hμX⟩ := internal_monoidal Λ X
  let := lY
  let := lX
  let F := internalDerivedPullback Λ f
  let L := derivedPullback Λ f
  let q := (derivedEquivalence Λ Y).functor
  let r := (derivedEquivalence Λ X).functor
  let ε := (derivedPullComparison Λ f).inv
  let μ' : MonoidalCategory.tensor (DerivedCategory (modules Λ Y)) ⋙ L ⟶
      L.prod L ⋙ MonoidalCategory.tensor (DerivedCategory (modules Λ X)) := μ
  let v' := L.map (regular Λ Y).hom ≫ v ≫ (regular Λ X).inv
  intro δ w hc
  have hp (P Q : DerivedCategory (internalModules Λ Y)) :
      μ'.app (q.obj P, q.obj Q) ≫ (ε.app P ⊗ₘ ε.app Q) ≫
        Functor.LaxMonoidal.μ r (F.obj P) (F.obj Q) =
      L.map (Functor.LaxMonoidal.μ q P Q) ≫ ε.app (P ⊗ Q) ≫
        r.map ((δ.app P).app Q) := by
    simpa only [q, r, F, L, ε, μ', hμY, hμX, pairModel, Category.assoc] using
      hc.1 ⟨P, trivial⟩ ⟨Q, trivial⟩
  have hs : Functor.LaxMonoidal.μ q = internalModelTensor Λ Y :=
    funext fun P ↦ funext fun Q ↦ hμY P Q
  have ht : Functor.LaxMonoidal.μ r = internalModelTensor Λ X :=
    funext fun P ↦ funext fun Q ↦ hμX P Q
  constructor
  · intro M N H
    simpa only [hs, ht, q, r, F, L, ε, μ', InternalEdges] using
      generic_edges F L q r ε (fun P Q ↦ (δ.app P).app Q) μ' hp M N H
  · intro M
    have he := generic_unit_edges F L q r ε (fun P Q ↦ (δ.app P).app Q) w
      (Iso.refl _) (Iso.refl _) hεY.symm hεX.symm
      (fun P Q ↦ μ'.app (P, Q)) v' hp hc.2 M
    have hlaws := section_unit_laws Λ f μ v h
    have hl : leftUnitPath L q r (Iso.refl _)
        (fun P Q ↦ μ'.app (P, Q)) v' (q.obj M) =
          L.map (regularLeft q (Iso.refl _) (q.obj M)) := by
      dsimp only [leftUnitPath, regularLeft, Iso.refl_inv]
      erw [id_whiskerRight, Category.id_comp, id_whiskerRight, Category.id_comp]
      exact hlaws.1 (q.obj M)
    have hr : rightUnitPath L q r (Iso.refl _)
        (fun P Q ↦ μ'.app (P, Q)) v' (q.obj M) =
          L.map (regularRight q (Iso.refl _) (q.obj M)) := by
      dsimp only [rightUnitPath, regularRight, Iso.refl_inv]
      erw [whiskerLeft_id, Category.id_comp, whiskerLeft_id, Category.id_comp]
      exact hlaws.2 (q.obj M)
    have hu := units_from_edges_and_laws F L q r ε (fun P Q ↦ (δ.app P).app Q) w
        (Iso.refl _) (Iso.refl _) (fun P Q ↦ μ'.app (P, Q)) v'
        (Functor.LaxMonoidal.μ q) (Functor.LaxMonoidal.μ r) M he hl hr
    with_unfolding_all
      simp only [hs, ht, q, r, F, L, ε, μ', v', InternalUnits, cast_eq] at hu ⊢
      exact hu

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
