/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalKoszulDualTerms
import all WeilConjectures.AlgebraicGeometry.PrincipalKoszulDualDifferential

/-! # Singleton dual transitions and the degree-zero unit

Source: Stacks Project, algebraization.tex, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PrincipalKoszulDualTerms
open MonoidalCategory
attribute [local irreducible] homComplexFunctor homComplexπ
  SheafOfModules.homObj SheafOfModules.homObjMap
  SheafOfModules.homFunctor SheafOfModules.homObjUnitIso
  projectionTermIso dualFactorTerm dualZeroTerm dualNegOneTerm
  coneZeroTerm coneNegOneTerm finiteDualTerm
  ringedKoszulFactorStep ringedKoszulFactorProjection
  HomologicalComplex.singleObjXSelf
  HomologicalComplex.doubleXIso₀ HomologicalComplex.doubleXIso₁
  CochainComplex.mappingCone.inl CochainComplex.mappingCone.inr
  CochainComplex.mappingCone.fst CochainComplex.mappingCone.snd

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})
variable (a : (SheafOfModules.unit
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)

attribute [local instance 20000] ringedCompletionHasSheafCompose
attribute [local irreducible] ringedHomUnitEvaluationIso

private theorem projectionTermIso_map
    {L L' : ringedSiteComplex R} (f : L' ⟶ L) (p q : ℤ) (h : p + q = 0) :
    (((homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)).map f.op).f q ≫
        (projectionTermIso R L' p q h).hom =
      (projectionTermIso R L p q h).hom ≫
        SheafOfModules.homObjMap (R := R) (f.f p) (𝟙 _) := by
  rw [projectionTermIso_hom R L' p q h, projectionTermIso_hom R L p q h]
  let F : homComplex (R := R) L (ringedSiteRingComplex R) ⟶
      homComplex (R := R) L' (ringedSiteRingComplex R) :=
    ((homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)).map f.op
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  change F.f q ≫ (homComplexπ L' (ringedSiteRingComplex R) q p 0 h ≫
      SheafOfModules.homObjMap (R := R) (𝟙 _) e.hom) =
    (homComplexπ L (ringedSiteRingComplex R) q p 0 h ≫
      SheafOfModules.homObjMap (R := R) (𝟙 _) e.hom) ≫ _
  have hf := homComplexFunctor_map_f_π (R := R) f (𝟙 (ringedSiteRingComplex R)) q p 0 h
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at hf
  change F.f q ≫ homComplexπ L' (ringedSiteRingComplex R) q p 0 h =
    homComplexπ L (ringedSiteRingComplex R) q p 0 h ≫
      SheafOfModules.homObjMap (R := R) (f.f p) (𝟙 _) at hf
  erw [← Category.assoc, hf]
  simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap (R := R),
    Category.id_comp, Category.comp_id]

private theorem singletonRemoveUnit_step (m : ℕ) :
    (ringedKoszulDiagram R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
        (homOfLE (Nat.le_succ m)) ≫ (singletonRemoveUnit R a (m + 1)).hom =
      (singletonRemoveUnit R a m).hom ≫
        ringedKoszulFactorStep R ⟨a.val, a.property⟩ m := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  change ((((ringedKoszulTensor R).map
      ((ringedKoszulFactors R ⟨a.val, a.property⟩).map
        (homOfLE (Nat.le_succ m))))).app (ringedSiteRingComplex R) ≫
      ((ringedKoszulTensor R).obj _).map (𝟙 _)) ≫ _ = _
  erw [Functor.map_id, Category.comp_id,
    show (ringedKoszulFactors R ⟨a.val, a.property⟩).map
      (homOfLE (Nat.le_succ m)) = ringedKoszulFactorStep R ⟨a.val, a.property⟩ m from
        Functor.ofSequence_map_homOfLE_succ _ m]
  exact MonoidalCategory.rightUnitor_naturality
    (ringedKoszulFactorStep R ⟨a.val, a.property⟩ m)

private theorem projectedTransport
    {A B : Type*} [Category* A] [Category* B] (F : Aᵒᵖ ⥤ B)
    {X₀ X₁ Y₀ Y₁ : A} (r₀ : X₀ ≅ Y₀) (r₁ : X₁ ≅ Y₁)
    (t : X₀ ⟶ X₁) (f : Y₀ ⟶ Y₁) (h : r₀.inv ≫ t = f ≫ r₁.inv)
    {P₀ P₁ : B} (p₀ : F.obj (op Y₀) ⟶ P₀) (p₁ : F.obj (op Y₁) ⟶ P₁)
    (k : P₁ ⟶ P₀) (hp : F.map f.op ≫ p₀ = p₁ ≫ k) :
    F.map t.op ≫ (F.map r₀.inv.op ≫ p₀) = (F.map r₁.inv.op ≫ p₁) ≫ k := by
  rw [← Category.assoc, ← F.map_comp, ← op_comp, h, op_comp, F.map_comp,
    Category.assoc, hp, ← Category.assoc]

private theorem dualFactorTerm_step (m : ℕ) (q : ℤ) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
        (homOfLE (Nat.le_succ m)).op).f q ≫ (dualFactorTerm R a m q).hom =
      (dualFactorTerm R a (m + 1) q).hom ≫
        SheafOfModules.homObjMap (R := R)
          ((ringedKoszulFactorStep R ⟨a.val, a.property⟩ m).f (-q)) (𝟙 _) := by
  rw [dualFactorTerm_hom R a m q, dualFactorTerm_hom R a (m + 1) q]
  let U := ringedSiteRingComplex R
  let D := (homComplexFunctor (R := R)).flip.obj U
  let r0 := singletonRemoveUnit R a m
  let r1 := singletonRemoveUnit R a (m + 1)
  let t := (ringedKoszulDiagram R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
    (homOfLE (Nat.le_succ m))
  let f := ringedKoszulFactorStep R ⟨a.val, a.property⟩ m
  have hpos : r0.inv ≫ t = f ≫ r1.inv := by
    apply (cancel_mono r1.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [singletonRemoveUnit_step R a m]
    exact r0.inv_hom_id_assoc f
  exact projectedTransport
    (D ⋙ HomologicalComplex.eval _ (.up ℤ) q) r0 r1 t f hpos
    (projectionTermIso R _ (-q) q (by omega)).hom
    (projectionTermIso R _ (-q) q (by omega)).hom
    (SheafOfModules.homObjMap (R := R) (f.f (-q)) (𝟙 _))
    (projectionTermIso_map R f (-q) q (by omega))

private theorem singletonRemoveUnit_projection (m : ℕ) :
    ringedKoszulProjection R 1 (fun _ ↦ ⟨a.val, a.property⟩) m =
      (singletonRemoveUnit R a m).hom ≫
        ringedKoszulFactorProjection R ⟨a.val, a.property⟩ m := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed R).2.1
  change ((ringedKoszulTensor R).map
      (ringedKoszulFactorProjection R ⟨a.val, a.property⟩ m)).app _ ≫
        ((ringedKoszulTensor R).obj _).map (𝟙 _) ≫ _ = _
  erw [Functor.map_id, Category.id_comp]
  change ((ringedKoszulFactorProjection R ⟨a.val, a.property⟩ m) ⊗ₘ 𝟙 _) ≫
      (λ_ (𝟙_ (ringedSiteComplex R))).hom =
    (ρ_ _).hom ≫ ringedKoszulFactorProjection R ⟨a.val, a.property⟩ m
  erw [MonoidalCategory.unitors_equal]
  exact MonoidalCategory.rightUnitor_naturality
    (ringedKoszulFactorProjection R ⟨a.val, a.property⟩ m)

attribute [local irreducible] singletonRemoveUnit

private theorem evaluateSquare
    {A : Type*} [Category* A] {X Y Z W : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : X ⟶ Z) (c : Z ⟶ Z)
    (e : Z ⟶ W) (d : W ⟶ W) (h : f ≫ g = s ≫ c) (hc : c ≫ e = e ≫ d) :
    f ≫ (g ≫ e) = (s ≫ e) ≫ d := by
  rw [← Category.assoc, h, Category.assoc, hc, ← Category.assoc]

private theorem homTransportEvaluation
    {A B : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (s : A ≅ SheafOfModules.unit _)
    (t : B ≅ SheafOfModules.unit _) (f : A ⟶ B)
    (c : SheafOfModules.unit _ ⟶ SheafOfModules.unit _)
    (h : s.inv ≫ f = c ≫ t.inv) :
    SheafOfModules.homObjMap (R := R) f (𝟙 _) ≫
        (SheafOfModules.homObjMap (R := R) s.inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom) =
      (SheafOfModules.homObjMap (R := R) t.inv (𝟙 _) ≫
        (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom) ≫ c := by
  let O := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let e := (SheafOfModules.homObjUnitIso (R := R) O).hom
  have hcomp :
      SheafOfModules.homObjMap (R := R) f (𝟙 O) ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 O) =
      SheafOfModules.homObjMap (R := R) t.inv (𝟙 O) ≫
        SheafOfModules.homObjMap (R := R) c (𝟙 O) := by
    simp only [SheafOfModules.homObjMap_comp_homObjMap (R := R), Category.comp_id, h]
  exact evaluateSquare
    (SheafOfModules.homObjMap (R := R) f (𝟙 O))
    (SheafOfModules.homObjMap (R := R) s.inv (𝟙 O))
    (SheafOfModules.homObjMap (R := R) t.inv (𝟙 O))
    (SheafOfModules.homObjMap (R := R) c (𝟙 O)) e c hcomp (transposeUnitScalar R c)

private theorem conjugateSquare
    {A : Type*} [Category* A] {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : A}
    (c₀ : X₀ ≅ Z₀) (c₁ : X₁ ≅ Z₁) (d₀ : Y₀ ≅ Z₀) (d₁ : Y₁ ≅ Z₁)
    (f : X₁ ⟶ X₀) (g : Y₁ ⟶ Y₀) (h : Z₁ ⟶ Z₀)
    (hc : f ≫ c₀.hom = c₁.hom ≫ h) (hd : g ≫ d₀.hom = d₁.hom ≫ h) :
    f ≫ (c₀.hom ≫ d₀.inv) = (c₁.hom ≫ d₁.inv) ≫ g := by
  apply (cancel_mono d₀.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hd, Iso.inv_hom_id_assoc, hc]

private theorem dualTermStep (m : ℕ) (q : ℤ)
    (s0 : (ringedKoszulFactor R ⟨a.val, a.property⟩ m).X (-q) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (s1 : (ringedKoszulFactor R ⟨a.val, a.property⟩ (m + 1)).X (-q) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (c : End (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hf : s0.inv ≫ (ringedKoszulFactorStep R ⟨a.val, a.property⟩ m).f (-q) =
      c.asHom ≫ s1.inv) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
        (homOfLE (Nat.le_succ m)).op).f q ≫
        ((dualFactorTerm R a m q).hom ≫
          SheafOfModules.homObjMap (R := R) s0.inv (𝟙 _) ≫
            (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom) =
      ((dualFactorTerm R a (m + 1) q).hom ≫
        SheafOfModules.homObjMap (R := R) s1.inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom) ≫ c.asHom := by
  rw [← Category.assoc, dualFactorTerm_step R a m q, Category.assoc,
    homTransportEvaluation R s0 s1 _ c.asHom hf, ← Category.assoc]

private theorem dualZeroTerm_step (m : ℕ) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
        (homOfLE (Nat.le_succ m)).op).f 0 ≫ (dualZeroTerm R a m).hom =
      (dualZeroTerm R a (m + 1)).hom := by
  rw [dualZeroTerm_hom R a m, dualZeroTerm_hom R a (m + 1)]
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let L0 := ringedKoszulFactor R ⟨a.val, a.property⟩ m
  let L1 := ringedKoszulFactor R ⟨a.val, a.property⟩ (m + 1)
  let s0 : L0.X 0 ≅ U := HomologicalComplex.doubleXIso₀ _ _
  let s1 : L1.X 0 ≅ U := HomologicalComplex.doubleXIso₀ _ _
  let f := ringedKoszulFactorStep R ⟨a.val, a.property⟩ m
  let e := SheafOfModules.homObjUnitIso (R := R) U
  have hf : s0.inv ≫ f.f 0 = s1.inv := by
    simp only [f, ringedKoszulFactorStep, ringedKoszulFactorStepF, dite_eq_left rfl,
      eqToHom_refl, Category.id_comp]
    change s0.inv ≫ (s0.hom ≫ s1.inv) = s1.inv
    exact s0.inv_hom_id_assoc _
  have hs := dualTermStep R a m 0
  have ht := hs s0 s1 (1 : End U) (by
    exact hf.trans (Category.id_comp s1.inv).symm)
  change _ ≫ ((dualFactorTerm R a m 0).hom ≫
      SheafOfModules.homObjMap (R := R) s0.inv (𝟙 U) ≫ e.hom) =
    (dualFactorTerm R a (m + 1) 0).hom ≫
      SheafOfModules.homObjMap (R := R) s1.inv (𝟙 U) ≫ e.hom
  exact ht.trans (Category.comp_id _)

private theorem dualNegOneTerm_step (m : ℕ) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
        (homOfLE (Nat.le_succ m)).op).f (-1) ≫ (dualNegOneTerm R a m).hom =
      (dualNegOneTerm R a (m + 1)).hom ≫ (ringedKoszulScalar R ⟨a.val, a.property⟩).asHom := by
  rw [dualNegOneTerm_hom R a m, dualNegOneTerm_hom R a (m + 1)]
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let L0 := ringedKoszulFactor R ⟨a.val, a.property⟩ m
  let L1 := ringedKoszulFactor R ⟨a.val, a.property⟩ (m + 1)
  let s0 : L0.X 1 ≅ U := HomologicalComplex.doubleXIso₁ _ _ (by decide)
  let s1 : L1.X 1 ≅ U := HomologicalComplex.doubleXIso₁ _ _ (by decide)
  let f := ringedKoszulFactorStep R ⟨a.val, a.property⟩ m
  let c := ringedKoszulScalar R ⟨a.val, a.property⟩
  let e := SheafOfModules.homObjUnitIso (R := R) U
  have hf : s0.inv ≫ f.f 1 = c.asHom ≫ s1.inv := by
    simp only [f, ringedKoszulFactorStep, ringedKoszulFactorStepF,
      dite_eq_right (show (1 : ℤ) ≠ 0 by decide), dite_eq_left rfl, eqToHom_refl,
      Category.id_comp]
    change s0.inv ≫ (s0.hom ≫ c.asHom ≫ s1.inv) = c.asHom ≫ s1.inv
    exact s0.inv_hom_id_assoc _
  have hs := dualTermStep R a m (-1)
  exact hs s0 s1 c hf

private theorem coneMap_snd
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {F₁ G₁ F₂ G₂ : CochainComplex A ℤ}
    (φ₁ : F₁ ⟶ G₁) (φ₂ : F₂ ⟶ G₂) (a : F₁ ⟶ F₂) (b : G₁ ⟶ G₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (q : ℤ) :
    (CochainComplex.mappingCone.map φ₁ φ₂ a b h).f q ≫
        (CochainComplex.mappingCone.snd φ₂).v q q (add_zero q) =
      (CochainComplex.mappingCone.snd φ₁).v q q (add_zero q) ≫ b.f q := by
  apply CochainComplex.mappingCone.ext_from φ₁ (q + 1) q rfl
  · simp only [Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc,
      CochainComplex.mappingCone.inl_v_snd_v,
      CochainComplex.mappingCone.inl_v_snd_v_assoc, comp_zero, zero_comp]
  · simp only [Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f,
      Category.assoc, CochainComplex.mappingCone.inr_f_snd_v,
      CochainComplex.mappingCone.inr_f_snd_v_assoc, Category.comp_id]

private theorem coneMap_fst
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {F₁ G₁ F₂ G₂ : CochainComplex A ℤ}
    (φ₁ : F₁ ⟶ G₁) (φ₂ : F₂ ⟶ G₂) (a : F₁ ⟶ F₂) (b : G₁ ⟶ G₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (q r : ℤ) (hqr : q + 1 = r) :
    (CochainComplex.mappingCone.map φ₁ φ₂ a b h).f q ≫
        (CochainComplex.mappingCone.fst φ₂).1.v q r hqr =
      (CochainComplex.mappingCone.fst φ₁).1.v q r hqr ≫ a.f r := by
  apply CochainComplex.mappingCone.ext_from φ₁ r q hqr
  · simp only [Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc,
      CochainComplex.mappingCone.inl_v_fst_v,
      CochainComplex.mappingCone.inl_v_fst_v_assoc, Category.comp_id]
  · simp only [Category.assoc, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f,
      Category.assoc, CochainComplex.mappingCone.inr_f_fst_v,
      CochainComplex.mappingCone.inr_f_fst_v_assoc, comp_zero, zero_comp]

section ConeStep
attribute [local irreducible] CochainComplex.mappingCone CochainComplex.mappingCone.map

private theorem coneSnd_step (m : ℕ) (q : ℤ) :
    (principalKoszulTransition R a m).f q ≫
        (CochainComplex.mappingCone.snd (scalarComplex R a m)).v q q (add_zero q) =
      (CochainComplex.mappingCone.snd (scalarComplex R a (m + 1))).v q q
        (add_zero q) := by
  have h := coneMap_snd (scalarComplex R a (m + 1)) (scalarComplex R a m)
      ((CochainComplex.singleFunctor _ 0).map (globalSectionMultiplication R a))
      (𝟙 _) (principalKoszul_transition_square R a m) q
  erw [HomologicalComplex.id_f, Category.comp_id] at h
  exact h

private theorem coneFst_step (m : ℕ) :
    (principalKoszulTransition R a m).f (-1) ≫
        (CochainComplex.mappingCone.fst (scalarComplex R a m)).1.v (-1) 0 (by decide) =
      (CochainComplex.mappingCone.fst (scalarComplex R a (m + 1))).1.v (-1) 0
        (by decide) ≫
      ((CochainComplex.singleFunctor _ 0).map
        (globalSectionMultiplication R a)).f 0 := by
  exact coneMap_fst (scalarComplex R a (m + 1)) (scalarComplex R a m)
    ((CochainComplex.singleFunctor _ 0).map (globalSectionMultiplication R a))
    (𝟙 _) (principalKoszul_transition_square R a m)
    (-1) 0 (by decide)

end ConeStep

private theorem coneZeroTerm_step (m : ℕ) :
    (principalKoszulTransition R a m).f 0 ≫ (coneZeroTerm R a m).hom =
      (coneZeroTerm R a (m + 1)).hom := by
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  have hc (k : ℕ) : (coneZeroTerm R a k).hom =
      (CochainComplex.mappingCone.snd (scalarComplex R a k)).v 0 0 (by decide) ≫
        e.hom := by
    unfold CochainComplex.mappingCone.snd
    change _ = HomologicalComplex.homotopyCofiber.sndX (scalarComplex R a k) 0 ≫ e.hom
    exact coneZeroProjection R a k
  rw [hc m, hc (m + 1)]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun g ↦ g ≫ e.hom) (coneSnd_step R a m 0))

private theorem coneNegOneTerm_step (m : ℕ) :
    (principalKoszulTransition R a m).f (-1) ≫ (coneNegOneTerm R a m).hom =
      (coneNegOneTerm R a (m + 1)).hom ≫ (ringedKoszulScalar R ⟨a.val, a.property⟩).asHom := by
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  have hc (k : ℕ) : (coneNegOneTerm R a k).hom =
      (CochainComplex.mappingCone.fst (scalarComplex R a k)).1.v (-1) 0
        (by decide) ≫ e.hom := by
    unfold coneNegOneTerm CochainComplex.mappingCone.fst
    change (HomologicalComplex.homotopyCofiber.XIsoBiprod (scalarComplex R a k)
        (-1) 0 negOneZeroRel).hom ≫ (biprod.fst ≫ e.hom) =
      ((HomologicalComplex.homotopyCofiber.XIsoBiprod (scalarComplex R a k)
        (-1) 0 negOneZeroRel).hom ≫ biprod.fst) ≫ e.hom
    exact (Category.assoc _ _ _).symm
  rw [hc m, hc (m + 1)]
  have he : ((CochainComplex.singleFunctor _ 0).map
      (globalSectionMultiplication R a)).f 0 ≫ e.hom =
        e.hom ≫ (ringedKoszulScalar R ⟨a.val, a.property⟩).asHom :=
    (HomologicalComplex.singleCompEvalIsoSelf _ (.up ℤ) 0).hom.naturality
      (globalSectionMultiplication R a)
  exact evaluateSquare _ _ _ _ _ _ (coneFst_step R a m) he

private theorem finiteDualTerm_step (m : ℕ) (q : ℤ) (hq : q = 0 ∨ q = -1) :
    (principalKoszulTransition R a m).f q ≫ (finiteDualTerm R a m q).hom =
      (finiteDualTerm R a (m + 1) q).hom ≫
        ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
          (homOfLE (Nat.le_succ m)).op).f q := by
  rcases hq with rfl | rfl
  · have h (k : ℕ) : (finiteDualTerm R a k 0).hom =
        (coneZeroTerm R a k).hom ≫ (dualZeroTerm R a k).inv := by
      simp [finiteDualTerm]
    rw [h m, h (m + 1)]
    exact conjugateSquare (coneZeroTerm R a m) (coneZeroTerm R a (m + 1))
      (dualZeroTerm R a m) (dualZeroTerm R a (m + 1)) _ _ (𝟙 _)
      (by simpa only [Category.comp_id] using coneZeroTerm_step R a m)
      (by simpa only [Category.comp_id] using dualZeroTerm_step R a m)
  · have h (k : ℕ) : (finiteDualTerm R a k (-1)).hom =
        (coneNegOneTerm R a k).hom ≫ (dualNegOneTerm R a k).inv := by
      simp [finiteDualTerm]
    rw [h m, h (m + 1)]
    exact conjugateSquare (coneNegOneTerm R a m) (coneNegOneTerm R a (m + 1))
      (dualNegOneTerm R a m) (dualNegOneTerm R a (m + 1)) _ _
      (ringedKoszulScalar R ⟨a.val, a.property⟩).asHom
      (coneNegOneTerm_step R a m) (dualNegOneTerm_step R a m)

private theorem dualUnit_remove (m : ℕ) :
    ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m ≫
        (((homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)).map
          (singletonRemoveUnit R a m).inv.op) =
      (ringedHomUnitEvaluationIso R (ringedSiteRingComplex R)).inv ≫
        (((homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)).map
          (ringedKoszulFactorProjection R ⟨a.val, a.property⟩ m).op) := by
  let D := (homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)
  change (_ ≫ D.map (ringedKoszulProjection R 1
      (fun _ ↦ ⟨a.val, a.property⟩) m).op) ≫
    D.map (singletonRemoveUnit R a m).inv.op = _
  erw [Category.assoc, ← D.map_comp, ← op_comp, singletonRemoveUnit_projection R a m,
    Iso.inv_hom_id_assoc]
  rfl

private theorem homEvaluationInterchange
    {A : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (s : A ≅ SheafOfModules.unit _) :
    (SheafOfModules.homObjMap (R := R) (𝟙 A) s.hom ≫
      SheafOfModules.homObjMap (R := R) s.inv (𝟙 _) ≫
        (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom) =
      (SheafOfModules.homObjMap (R := R) s.inv (𝟙 A) ≫
        (SheafOfModules.homObjUnitIso (R := R) A).hom) ≫ s.hom := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  unfold SheafOfModules.homObjMap SheafOfModules.homObjUnitIso
  rfl

section

private theorem ringedEvaluationComponent (M : ringedSiteComplex R) (n : ℤ) :
    (ringedHomUnitEvaluationIso R M).hom.f n =
      homComplexπ (ringedSiteRingComplex R) M n 0 n (zero_add n) ≫
        SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).inv (𝟙 (M.X n)) ≫
          (SheafOfModules.homObjUnitIso (R := R) (M.X n)).hom := by
  exact ringedHomUnitEvaluationIso_hom_f_projection R M n

private theorem unitDoubleEvaluation :
    let U := ringedSiteRingComplex R
    let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (projectionTermIso R U 0 0 (by decide)).hom ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom =
      (ringedHomUnitEvaluationIso R U).hom.f 0 ≫ s.hom := by
  dsimp only
  rw [projectionTermIso_hom R (ringedSiteRingComplex R) 0 0 (by decide)]
  let U := ringedSiteRingComplex R
  let O := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let s : U.X 0 ≅ O := HomologicalComplex.singleObjXSelf (.up ℤ) 0 _
  have he : (ringedHomUnitEvaluationIso R U).hom.f 0 =
      homComplexπ U U 0 0 0 (by decide) ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := R) (U.X 0)).hom :=
    ringedEvaluationComponent R U 0
  erw [he]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ homComplexπ U U 0 0 0 (by decide) ≫ f) (homEvaluationInterchange R s)

end

private theorem unitAssembly
    {A : Type*} [Category A] {X Y B L V W H O : A}
    (E : B ≅ X) (g : X ⟶ Y) (ψ : Y ⟶ L) (f : B ⟶ L)
    (p0 : L ⟶ V) (p1 : B ⟶ W) (k : W ⟶ V) (d : V ⟶ H)
    (s : W ⟶ H) (e : H ⟶ O) (t : X ⟶ O)
    (hr : g ≫ ψ = E.inv ≫ f) (hn : f ≫ p0 = p1 ≫ k)
    (hp : k ≫ d = s) (hu : p1 ≫ s ≫ e = E.hom ≫ t) :
    g ≫ (ψ ≫ p0 ≫ d ≫ e) = t := by
  rw [← Category.assoc, hr]
  simp only [Category.assoc]
  rw [← Category.assoc f p0, hn]
  simp only [Category.assoc]
  rw [← Category.assoc k d, hp, hu, E.inv_hom_id_assoc]

private theorem unitInverseSquare
    {A : Type*} [Category A] {X Y U Z : A}
    (c : X ≅ Z) (d : Y ≅ Z) (f : U ⟶ X) (g : U ⟶ Y)
    (h : f ≫ c.hom = g ≫ d.hom) :
    f ≫ (c.hom ≫ d.inv) = g := by
  rw [← Category.assoc, h, Category.assoc, d.hom_inv_id, Category.comp_id]

private theorem dualZeroTerm_unit (m : ℕ) :
    (ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m).f 0 ≫
        (dualZeroTerm R a m).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).hom := by
  rw [dualZeroTerm_hom R a m, dualFactorTerm_hom R a m 0]
  let O := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let U := ringedSiteRingComplex R
  let L := ringedKoszulFactor R ⟨a.val, a.property⟩ m
  let s : U.X 0 ≅ O := HomologicalComplex.singleObjXSelf (.up ℤ) 0 _
  let d : L.X 0 ≅ O := HomologicalComplex.doubleXIso₀ _ _
  let p : L ⟶ U := ringedKoszulFactorProjection R ⟨a.val, a.property⟩ m
  let D := (homComplexFunctor (R := R)).flip.obj U
  let E := ringedHomUnitEvaluationIso R U
  let ψ : ((ringedKoszulDualTower R 1
      (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)) ≅ homComplex (R := R) L U :=
    D.mapIso (singletonRemoveUnit R a m).symm.op
  let e := SheafOfModules.homObjUnitIso (R := R) O
  have hp : d.inv ≫ p.f 0 = s.inv := by
    simp only [p, ringedKoszulFactorProjection, ringedKoszulFactorProjectionF,
      dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id]
    change d.inv ≫ (d.hom ≫ s.inv) = s.inv
    exact d.inv_hom_id_assoc s.inv
  have hr : ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m ≫ ψ.hom =
      E.inv ≫ D.map p.op := dualUnit_remove R a m
  let F : homComplex (R := R) U U ⟶ homComplex (R := R) L U := D.map p.op
  have hr0 : (ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m).f 0 ≫
      ψ.hom.f 0 = E.inv.f 0 ≫ F.f 0 := by
    change ((ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m) ≫
      ψ.hom).f 0 = (E.inv ≫ F).f 0
    exact congrArg (fun h ↦ h.f 0) hr
  have hn : F.f 0 ≫ (projectionTermIso R L 0 0 (by decide)).hom =
      (projectionTermIso R U 0 0 (by decide)).hom ≫
        SheafOfModules.homObjMap (R := R) (p.f 0) (𝟙 O) :=
    projectionTermIso_map R p 0 0 (by decide)
  have hp' : SheafOfModules.homObjMap (R := R) (p.f 0) (𝟙 O) ≫
        SheafOfModules.homObjMap (R := R) d.inv (𝟙 O) =
      SheafOfModules.homObjMap (R := R) s.inv (𝟙 O) := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R), hp, Category.id_comp]
  change _ ≫ (ψ.hom.f 0 ≫ (projectionTermIso R L 0 0 (by decide)).hom ≫
      SheafOfModules.homObjMap (R := R) d.inv (𝟙 O) ≫ e.hom) = s.hom
  exact unitAssembly ((HomologicalComplex.eval _ (.up ℤ) 0).mapIso E)
    _ _ (F.f 0) _ _ _ _ _ _ s.hom hr0 hn hp' (unitDoubleEvaluation R)

private theorem finiteDualTerm_unit (m : ℕ) :
    (CochainComplex.mappingCone.inr (scalarComplex R a m)).f 0 ≫
        (finiteDualTerm R a m 0).hom =
      (ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m).f 0 := by
  have h : (finiteDualTerm R a m 0).hom =
      (coneZeroTerm R a m).hom ≫ (dualZeroTerm R a m).inv := by
    simp [finiteDualTerm]
  rw [h]
  apply unitInverseSquare (coneZeroTerm R a m) (dualZeroTerm R a m)
  erw [dualZeroTerm_unit R a m, coneZeroProjection R a m]
  unfold CochainComplex.mappingCone.inr
  change HomologicalComplex.homotopyCofiber.inrX (scalarComplex R a m) 0 ≫
    (HomologicalComplex.homotopyCofiber.sndX (scalarComplex R a m) 0 ≫ _) = _
  exact HomologicalComplex.homotopyCofiber.inrX_sndX_assoc (scalarComplex R a m) 0 _

/-- The explicit rank-one identifications preserve the two supported transition
components and the degree-zero unit component.

Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node).

Proof: naturality of the total-tensor right unitor removes the constant unit from
the positive singleton diagram, including its forward map. The positive map is
identity in degree zero and multiplication by a in degree one. The Hom product
projection formula for precomposition reverses these: evaluation at one makes the
negative degree-minus-one transition multiplication by a and the degree-zero
transition identity. The principal cone transition has these same two entries by
the mapping-cone map formula. Conjugate with the term isomorphisms to get the first
identity in each of its two degrees. For the second identity, the positive projection
is identity on the degree-zero unit. Its dual sends a scalar r to the functional
with value r at one. The inverse evaluation map in ringedKoszulDualUnit is precisely
this map. The cone inclusion is the inclusion of the same degree-zero summand;
the right-unitor naturality equation and equality of the two unit constraints on
the unit identify the singleton tensor projection with this map. Thus both composites
are the inverse of the same projection-and-evaluation isomorphism. These calculations
hold over the zero ring and empty sites as well as for zero or invertible a. -/
theorem finiteDualTerm_transition_unit :
    (∀ (m : ℕ) (q : ℤ), q = 0 ∨ q = -1 →
      (principalKoszulTransition R a m).f q ≫ (finiteDualTerm R a m q).hom =
        (finiteDualTerm R a (m + 1) q).hom ≫
          ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).map
            (homOfLE (Nat.le_succ m)).op).f q) ∧
    (∀ m : ℕ, (CochainComplex.mappingCone.inr (scalarComplex R a m)).f 0 ≫
        (finiteDualTerm R a m 0).hom =
      (ringedKoszulDualUnit R 1 (fun _ ↦ ⟨a.val, a.property⟩) m).f 0) := by
  exact ⟨finiteDualTerm_step R a, finiteDualTerm_unit R a⟩

end CategoryTheory.PrincipalKoszulDualTerms
