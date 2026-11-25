/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Functorial short exact presentations of mapping cones

## References

* Stacks Project, Derived Categories, Tags 013N, 014G and 013O (the cylinder factorization and its
  homotopy equivalence), applied functorially to a square
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
variable {C : Type u} [Category C] [Abelian C]
variable {A B A' B' : CochainComplex C ℤ}

private abbrev cyl (_t : A ⟶ B) := B ⊞ mappingCone (𝟙 A)
private def cylI (t : A ⟶ B) : A ⟶ cyl t := biprod.lift t (mappingCone.inr (𝟙 A))
private def cylQ (t : A ⟶ B) : cyl t ⟶ mappingCone t :=
  biprod.desc (mappingCone.inr t) (-mappingCone.map (𝟙 A) t (𝟙 A) t (by simp))
private lemma cyl_zero (t : A ⟶ B) : cylI t ≫ cylQ t = 0 := by
  dsimp [cylI, cylQ]
  simp only [biprod.lift_desc, Preadditive.comp_neg]
  have h := (mappingCone.triangleMap (𝟙 A) t (𝟙 A) t (by simp)).comm₂
  change mappingCone.inr (𝟙 A) ≫
    mappingCone.map (𝟙 A) t (𝟙 A) t (by simp) = t ≫ mappingCone.inr t at h
  rw [h, add_neg_cancel]
private def cylRow (t : A ⟶ B) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (cylI t) (cylQ t) (cyl_zero t)

private lemma cyl_exact (t : A ⟶ B) : (cylRow t).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let r : (cyl t).X n ⟶ A.X n :=
    (biprod.snd : cyl t ⟶ mappingCone (𝟙 A)).f n ≫
      (mappingCone.snd (𝟙 A)).v n n (by omega)
  let s : (mappingCone t).X n ⟶ (cyl t).X n :=
    (mappingCone.snd t).v n n (by omega) ≫ (biprod.inl : B ⟶ cyl t).f n -
      (mappingCone.fst t).1.v n (n + 1) rfl ≫
        (mappingCone.inl (𝟙 A)).v (n + 1) n (by omega) ≫
          (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := s, f_r := ?_, s_g := ?_, id := ?_ }
  · change (cylI t).f n ≫ r = 𝟙 _
    dsimp only [r]
    rw [← Category.assoc, ← HomologicalComplex.comp_f]
    simp only [cylI, biprod.lift_snd, mappingCone.inr_f_snd_v]
  · change s ≫ (cylQ t).f n = 𝟙 _
    apply mappingCone.ext_from t (n + 1) n rfl
    all_goals dsimp only [s]
    all_goals simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
      Category.comp_id, zero_comp, sub_zero, zero_sub]
    all_goals simp only [← HomologicalComplex.comp_f, cylQ, biprod.inl_desc, biprod.inr_desc]
    all_goals simp [mappingCone.map]
  · change r ≫ (cylI t).f n + (cylQ t).f n ≫ s = 𝟙 _
    have hlq : (biprod.inl : B ⟶ cyl t).f n ≫ (cylQ t).f n =
        (mappingCone.inr t).f n := by
      rw [← HomologicalComplex.comp_f]
      simp only [cylQ, biprod.inl_desc]
    have hrq : (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫ (cylQ t).f n =
        -(mappingCone.map (𝟙 A) t (𝟙 A) t (by simp)).f n := by
      rw [← HomologicalComplex.comp_f]
      simp only [cylQ, biprod.inr_desc, HomologicalComplex.neg_f_apply]
    have hlr : (biprod.inl : B ⟶ cyl t).f n ≫
        (biprod.snd : cyl t ⟶ mappingCone (𝟙 A)).f n = 0 := by
      rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]
    have hrr : (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫
        (biprod.snd : cyl t ⟶ mappingCone (𝟙 A)).f n = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]
    let F := HomologicalComplex.eval C (.up ℤ) n
    apply (cancel_epi (F.mapBiprod B (mappingCone (𝟙 A))).inv).mp
    apply biprod.hom_ext'
    · simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc, Preadditive.comp_add]
      change (biprod.inl : B ⟶ cyl t).f n ≫ r ≫ (cylI t).f n +
        (biprod.inl : B ⟶ cyl t).f n ≫ (cylQ t).f n ≫ s =
          (biprod.inl : B ⟶ cyl t).f n ≫ 𝟙 _
      dsimp only [r, s]
      simp only [Category.assoc, reassoc_of% hlr, zero_comp, zero_add,
        reassoc_of% hlq]
      simp
    · simp only [Functor.mapBiprod_inv, biprod.inr_desc_assoc, Preadditive.comp_add]
      change (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫
        r ≫ (cylI t).f n + (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫
          (cylQ t).f n ≫ s = (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t).f n ≫ 𝟙 _
      dsimp only [r]
      simp only [Category.assoc, reassoc_of% hrr,
        reassoc_of% hrq]
      apply mappingCone.ext_from (𝟙 A) (n + 1) n rfl
      all_goals dsimp only [s]
      all_goals simp [mappingCone.map, Category.assoc, cylI, biprod.lift_eq]

section
variable [HasDerivedCategory.{w} C]
private lemma coneId_map_zero (A : CochainComplex C ℤ)
    {D : CochainComplex C ℤ} (f : mappingCone (𝟙 A) ⟶ D) :
    DerivedCategory.Q.map f = 0 := by
  have hz := DerivedCategory.Q_map_eq_of_homotopy C (mappingCone.homotopyToZeroOfId A)
  have h := congrArg (fun k ↦ k ≫ DerivedCategory.Q.map f) hz
  simpa using h

private def cylIso (t : A ⟶ B) : DerivedCategory.Q.obj (cyl t) ≅ DerivedCategory.Q.obj B where
  hom := DerivedCategory.Q.map biprod.fst
  inv := DerivedCategory.Q.map biprod.inl
  hom_inv_id := by
    have hz := coneId_map_zero A (biprod.inr : mappingCone (𝟙 A) ⟶ cyl t)
    have h := congrArg (fun k ↦ DerivedCategory.Q.map k)
      (biprod.total (X := B) (Y := mappingCone (𝟙 A)))
    simp only [Functor.map_add, Functor.map_comp, CategoryTheory.Functor.map_id, hz,
      comp_zero, add_zero] at h
    exact h
  inv_hom_id := by rw [← Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id]

private lemma cyl_first (t : A ⟶ B) :
    DerivedCategory.Q.map (cylI t) ≫ (cylIso t).hom = DerivedCategory.Q.map t := by
  dsimp only [cylIso]
  rw [← Functor.map_comp]
  simp [cylI]

private lemma cyl_second (t : A ⟶ B) :
    DerivedCategory.Q.map (cylQ t) =
      (cylIso t).hom ≫ DerivedCategory.Q.map (mappingCone.inr t) := by
  have hz := coneId_map_zero A
    (mappingCone.map (𝟙 A) t (𝟙 A) t (by simp))
  rw [cylQ, biprod.desc_eq, Functor.map_add, Functor.map_comp, Functor.map_comp,
    Functor.map_neg, hz]
  simp [cylIso]

end

private def cylMap (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B') :
    cyl t ⟶ cyl t' :=
  biprod.map β (mappingCone.map (𝟙 A) (𝟙 A') α α (by simp))

private lemma cylMap_first (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
    (hc : t ≫ β = α ≫ t') : cylI t ≫ cylMap t t' α β = α ≫ cylI t' := by
  apply biprod.hom_ext
  · simp [cylI, cylMap, Category.assoc, hc]
  · dsimp only [cylI, cylMap]
    simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
    rw [biprod.lift_snd]
    exact (mappingCone.triangleMap (𝟙 A) (𝟙 A') α α (by simp)).comm₂

private lemma cylMap_second (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
    (hc : t ≫ β = α ≫ t') : cylMap t t' α β ≫ cylQ t' =
      cylQ t ≫ mappingCone.map t t' α β hc := by
  apply biprod.hom_ext'
  · dsimp only [cylMap, cylQ]
    simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
    exact (mappingCone.triangleMap t t' α β hc).comm₂.symm
  · dsimp only [cylMap, cylQ]
    simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
      Preadditive.comp_neg, Preadditive.neg_comp]
    congr 1
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    simp only [Category.id_comp, Category.comp_id, hc]

private def cylRowMap (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
    (hc : t ≫ β = α ≫ t') : cylRow t ⟶ cylRow t' where
  τ₁ := α
  τ₂ := cylMap t t' α β
  τ₃ := mappingCone.map t t' α β hc
  comm₁₂ := (cylMap_first t t' α β hc).symm
  comm₂₃ := cylMap_second t t' α β hc

/-- A strict square of chain maps has functorial short exact mapping-cylinder
presentations, with all three prescribed components after localization. -/
theorem cone_diagram_full_ses_presentation
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    (A B A' B' : CochainComplex C ℤ)
    (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
    (hc : t ≫ β = α ≫ t') :
    ∃ (P P' : ShortComplex (CochainComplex C ℤ)) (m : P ⟶ P')
      (d₁ : DerivedCategory.Q.obj P.X₁ ≅ DerivedCategory.Q.obj A)
      (d₂ : DerivedCategory.Q.obj P.X₂ ≅ DerivedCategory.Q.obj B)
      (d₃ : DerivedCategory.Q.obj P.X₃ ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone t))
      (d₁' : DerivedCategory.Q.obj P'.X₁ ≅ DerivedCategory.Q.obj A')
      (d₂' : DerivedCategory.Q.obj P'.X₂ ≅ DerivedCategory.Q.obj B')
      (d₃' : DerivedCategory.Q.obj P'.X₃ ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone t')),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map P.f ≫ d₂.hom = d₁.hom ≫ DerivedCategory.Q.map t ∧
      DerivedCategory.Q.map P.g ≫ d₃.hom =
        d₂.hom ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr t) ∧
      DerivedCategory.Q.map P'.f ≫ d₂'.hom = d₁'.hom ≫ DerivedCategory.Q.map t' ∧
      DerivedCategory.Q.map P'.g ≫ d₃'.hom =
        d₂'.hom ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr t') ∧
      DerivedCategory.Q.map m.τ₁ ≫ d₁'.hom = d₁.hom ≫ DerivedCategory.Q.map α ∧
      DerivedCategory.Q.map m.τ₂ ≫ d₂'.hom = d₂.hom ≫ DerivedCategory.Q.map β ∧
      DerivedCategory.Q.map m.τ₃ ≫ d₃'.hom =
        d₃.hom ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) :=
by
  refine ⟨cylRow t, cylRow t', cylRowMap t t' α β hc, Iso.refl _, cylIso t,
    Iso.refl _, Iso.refl _, cylIso t', Iso.refl _, cyl_exact t, cyl_exact t',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cylRow, Iso.refl_hom, Category.id_comp] using cyl_first t
  · simpa only [cylRow, Iso.refl_hom, Category.comp_id] using cyl_second t
  · simpa only [cylRow, Iso.refl_hom, Category.id_comp] using cyl_first t'
  · simpa only [cylRow, Iso.refl_hom, Category.comp_id] using cyl_second t'
  · simp [cylRowMap]
  · change DerivedCategory.Q.map (cylMap t t' α β) ≫
        DerivedCategory.Q.map biprod.fst =
      DerivedCategory.Q.map biprod.fst ≫ DerivedCategory.Q.map β
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp [cylMap]
  · simp [cylRowMap]
