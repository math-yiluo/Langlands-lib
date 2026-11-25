/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Algebra.Homology.FiniteStripConeFiltrationGradedPoint
import WeilConjectures.CategoryTheory.DegreewiseFiltration

/-! # Vertical filtration of a finite-strip augmentation cone

Source: Stacks Project, Homology, Lemma 12.25.4 (Tag 0133).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

/-- The finite sum of cone summands whose vertical degree is at least the cutoff. -/
private noncomputable def stripStep
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ) (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ)) (p n : ℤ) :
    Subobject ((CochainComplex.mappingCone b).X n) :=
  (if p ≤ n + 1 then imageSubobject
    ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
  (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
    if p ≤ n - i then imageSubobject
      (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
        (CochainComplex.mappingCone.inr b).f n) else ⊥)

/-- Increasing the cutoff removes generators. -/
private theorem stripStep_antitone
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ) (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ)) (n : ℤ) :
    Antitone (fun p ↦ stripStep K r A b p n) := by
  intro p q hpq
  unfold stripStep
  apply sup_le_sup
  · split_ifs with hq hp
    · exact le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · apply Finset.sup_le
    intro i hi
    apply le_trans _ (Finset.le_sup (f := fun i ↦
      if p ≤ n - i then imageSubobject
        (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
          (CochainComplex.mappingCone.inr b).f n) else ⊥) hi)
    split_ifs with hq hp
    · exact le_rfl
    · omega
    · exact bot_le
    · exact le_rfl

/-- Above all source and target vertical indices the step is empty. -/
private theorem stripStep_bot
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ) (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ)) (n : ℤ) :
    stripStep K r A b (n + 2) n = ⊥ := by
  unfold stripStep
  rw [ite_eq_right (by omega), bot_sup_eq]
  apply le_antisymm _ bot_le
  apply Finset.sup_le
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  rw [ite_eq_right (by omega)]

/-- A generating map factors through every subobject containing its image. -/
private theorem factors_image
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (a : X ⟶ Y) (Q : Subobject Y)
    (ha : imageSubobject a ≤ Q) : Q.Factors a := by
  apply Subobject.factors_of_le a ha
  simpa using imageSubobject_factors_comp_self a (𝟙 X)

/-- A map killing a subobject kills its generators. -/
private theorem comp_zero_of_image_le
    {C : Type u} [Category.{v} C] [Abelian C] {X Y Z : C} (a : X ⟶ Y) (S : Subobject Y) (g : Y ⟶ Z)
    (ha : imageSubobject a ≤ S) (hg : S.arrow ≫ g = 0) : a ≫ g = 0 := by
  have he : (factorThruImageSubobject a ≫ Subobject.ofLE _ S ha) ≫ S.arrow = a := by
    simp
  rw [← he, Category.assoc, hg, CategoryTheory.Limits.comp_zero]

/-- Outside the horizontal support every degree of the row is zero. -/
private theorem strip_row_isZero
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (r : ℕ) (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (i j : ℤ) (hi : i < 0 ∨ (r : ℤ) ≤ i) : IsZero ((K.X i).X j) :=
  (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero (hsupport i hi)

/-- The supported diagonal summands and source generate the entire cone term. -/
private theorem stripStep_top
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ)) (n : ℤ) :
    stripStep K r A b (n - (r : ℤ)) n = ⊤ := by
  let S := stripStep K r A b (n - (r : ℤ)) n
  have hsrc : imageSubobject
      ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) ≤ S := by
    dsimp [S, stripStep]
    rw [ite_eq_left (by omega)]
    exact le_sup_left
  have htgt (i : ℤ) (hi : i ∈ Finset.Ico (0 : ℤ) (r : ℤ)) : imageSubobject
      (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
        (CochainComplex.mappingCone.inr b).f n) ≤ S := by
    have hi' := Finset.mem_Ico.mp hi
    apply le_trans _ le_sup_right
    apply le_trans _ (Finset.le_sup (f := fun i ↦
      if n - (r : ℤ) ≤ n - i then imageSubobject
        (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
          (CochainComplex.mappingCone.inr b).f n) else ⊥) hi)
    rw [ite_eq_left (by omega)]
  have : Epi S.arrow := CategoryTheory.Preadditive.epi_of_cancel_zero S.arrow (by
    intro Y g hg
    apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
    · rw [CategoryTheory.Limits.comp_zero]
      exact comp_zero_of_image_le _ S g hsrc hg
    · rw [CategoryTheory.Limits.comp_zero]
      apply total.hom_ext
      intro i j hij
      by_cases hi : i ∈ Finset.Ico (0 : ℤ) (r : ℤ)
      · have hj : n - i = j := by change i + j = n at hij; omega
        have h := comp_zero_of_image_le _ S g (htgt i hi) hg
        rw [hj, K.ιTotalOrZero_eq _ _ _ _ hij] at h
        simpa only [Category.assoc, CategoryTheory.Limits.comp_zero] using h
      · have hz := strip_row_isZero K r hsupport i j (by
          simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
          exact hi)
        simpa only [CategoryTheory.Limits.comp_zero] using hz.eq_zero_of_src
          (K.ιTotal (ComplexShape.up ℤ) i j n hij ≫
            (CochainComplex.mappingCone.inr b).f n ≫ g))
  have : IsIso S.arrow := isIso_of_mono_of_epi S.arrow
  exact Subobject.eq_top_of_isIso_arrow S

/-- Scalar multiples preserve factorization through a subobject. -/
private theorem factors_zsmul
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (Q : Subobject Y) (a : X ⟶ Y)
    (z : ℤ) (ha : Q.Factors a) : Q.Factors (z • a) := by
  rw [← Subobject.factorThru_arrow Q a ha, ← CategoryTheory.Preadditive.zsmul_comp]
  exact Subobject.factors_comp_arrow _

/-- The source generator lies in the step when its vertical index meets the cutoff. -/
private theorem stripStep_source_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ) (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ)) (p n : ℤ) (hp : p ≤ n + 1) :
    (stripStep K r A b p n).Factors
      ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) := by
  apply factors_image
  unfold stripStep
  rw [ite_eq_left hp]
  exact le_sup_left

/-- Every supported target generator above the cutoff lies in the step. -/
private theorem stripStep_target_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (p n i j : ℤ) (hij : i + j = n) (hp : p ≤ j) :
    (stripStep K r A b p n).Factors
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j n ≫
        (CochainComplex.mappingCone.inr b).f n) := by
  by_cases hi : i ∈ Finset.Ico (0 : ℤ) (r : ℤ)
  · have hj : j = n - i := by omega
    subst j
    apply factors_image
    apply le_trans _ le_sup_right
    apply le_trans _ (Finset.le_sup (f := fun i ↦
      if p ≤ n - i then imageSubobject
        (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
          (CochainComplex.mappingCone.inr b).f n) else ⊥) hi)
    rw [ite_eq_left hp]
  · have hz := strip_row_isZero K r hsupport i j (by
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
      exact hi)
    rw [hz.eq_zero_of_src (K.ιTotalOrZero (ComplexShape.up ℤ) i j n)]
    simp only [CategoryTheory.Limits.zero_comp, Subobject.factors_zero]

/-- The total differential preserves or raises the vertical degree. -/
private theorem stripStep_target_d_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (p n i : ℤ) (hp : p ≤ n - i) :
    (stripStep K r A b p (n + 1)).Factors
      (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
        (K.total (ComplexShape.up ℤ)).d n (n + 1) ≫
        (CochainComplex.mappingCone.inr b).f (n + 1)) := by
  let Q := stripStep K r A b p (n + 1)
  have hsum : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i, n - i) = n := by change i + (n - i) = n; omega
  rw [K.ιTotalOrZero_eq _ _ _ _ hsum, total_d]
  simp only [CategoryTheory.Preadditive.comp_add, CategoryTheory.Preadditive.add_comp,
    ι_D₁_assoc, ι_D₂_assoc]
  rw [K.d₁_eq' _ (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
    K.d₂_eq' _ i (show (ComplexShape.up ℤ).Rel (n - i) ((n - i) + 1) by rfl)]
  simp only [Category.assoc, CategoryTheory.Linear.units_smul_comp]
  apply Subobject.factors_add
  · rw [Units.smul_def]
    apply factors_zsmul
    exact Subobject.factors_of_factors_right ((K.d i (i + 1)).f (n - i))
      (stripStep_target_factors K r hsupport A b p (n + 1) (i + 1) (n - i)
        (by omega) hp)
  · rw [Units.smul_def]
    apply factors_zsmul
    exact Subobject.factors_of_factors_right ((K.X i).d (n - i) ((n - i) + 1))
      (stripStep_target_factors K r hsupport A b p (n + 1) i ((n - i) + 1)
        (by omega) (by omega))

/-- The cone differential preserves the finite vertical tails. -/
private theorem stripStep_stable
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n)) (p n : ℤ) :
    (stripStep K r A b p (n + 1)).Factors
      ((stripStep K r A b p n).arrow ≫
        (CochainComplex.mappingCone b).d n (n + 1)) := by
  let d := (CochainComplex.mappingCone b).d n (n + 1)
  let Q := stripStep K r A b p (n + 1)
  let P := (Subobject.pullback d).obj Q
  have hle : stripStep K r A b p n ≤ P := by
    unfold stripStep
    apply sup_le
    · split_ifs with hp
      · let t := (CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)
        have ht : Q.Factors (t ≫ d) := by
          change Q.Factors (HomologicalComplex.homotopyCofiber.inlX b (n + 1) n rfl ≫
            HomologicalComplex.homotopyCofiber.d b n (n + 1))
          rw [HomologicalComplex.homotopyCofiber.inlX_d b n (n + 1) ((n + 1) + 1)
            rfl rfl]
          apply Subobject.factors_add
          · have h := Subobject.factors_of_factors_right (A.d (n + 1) ((n + 1) + 1))
              (stripStep_source_factors K r A b p (n + 1) (by omega))
            simpa only [neg_one_zsmul, CochainComplex.mappingCone.inl,
              CochainComplex.HomComplex.Cochain.mk_v] using factors_zsmul Q _ (-1) h
          · rw [hb]
            have h := stripStep_target_factors K r hsupport A b p (n + 1) 0 (n + 1)
              (by omega) hp
            rw [K.ιTotalOrZero_eq _ _ _ _ (Int.zero_add (n + 1))] at h
            simpa only [Category.assoc, CochainComplex.mappingCone.inr,
              HomologicalComplex.homotopyCofiber.inr_f] using
              Subobject.factors_of_factors_right (a (n + 1)) h
        have ht' := pullback_factors d Q t ht
        exact imageSubobject_le t (P.factorThru t ht') (Subobject.factorThru_arrow _ _ _)
      · exact bot_le
    · apply Finset.sup_le
      intro i hi
      split_ifs with hp
      · let t := K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
          (CochainComplex.mappingCone.inr b).f n
        have ht : Q.Factors (t ≫ d) := by
          dsimp only [t, d]
          rw [Category.assoc, HomologicalComplex.Hom.comm]
          exact stripStep_target_d_factors K r hsupport A b p n i hp
        have ht' := pullback_factors d Q t ht
        exact imageSubobject_le t (P.factorThru t ht') (Subobject.factorThru_arrow _ _ _)
      · exact bot_le
  apply (pullback_factors_iff d Q _).1
  exact Subobject.factors_of_le _ hle (Subobject.factors_self _)

/-- (blueprint: lem-sc-finite-strip-cone-filtration-steps)
Proof: construct the finite joins of source and target image subobjects, verify
stability under the cone differential, and use the support bounds to obtain the
two endpoint identities. -/
theorem finite_strip_cone_filtration_steps
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone b),
      (∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
          if p ≤ n - i then imageSubobject
            (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
              (CochainComplex.mappingCone.inr b).f n) else ⊥)) ∧
      (∀ n : ℤ, F.complexStep (n - (r : ℤ)) n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) := by
  have _ := hf
  obtain ⟨F, hF⟩ := CategoryTheory.Functor.filtration_of_degreewise (CochainComplex.mappingCone b)
    (stripStep K r A b) (stripStep_antitone K r A b)
    (stripStep_stable K r hsupport A a b hb)
  refine ⟨F, hF, ?_⟩
  intro n
  rw [hF, hF]
  exact ⟨stripStep_top K r hsupport A b n, stripStep_bot K r A b n⟩

/-- (blueprint: lem-sc-finite-strip-cone-filtration-graded)
Proof: quotient successive filtration steps, identify the surviving diagonal
with the translated row cone, and transport the resulting short-complex
homology isomorphism. -/
theorem finite_strip_cone_filtration_graded
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥)) :
      ∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone (f p)).homology (n - p)) := by
  intro p n
  obtain ⟨e⟩ := finite_strip_cone_filtration_graded_point K r hsupport A a b hb f hf F hsteps p n
  exact ⟨ShortComplex.homologyMapIso e⟩

/-- (blueprint: lem-sc-finite-strip-cone-filtration) -/
theorem finite_strip_cone_filtration
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (hf : ∀ p : ℤ, (f p).f 0 = (HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) 0 (A.X p)).hom ≫ a p) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone b),
      (∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
          if p ≤ n - i then imageSubobject
            (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
              (CochainComplex.mappingCone.inr b).f n) else ⊥)) ∧
      (∀ n : ℤ, F.complexStep (n - (r : ℤ)) n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      (∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone (f p)).homology (n - p))) := by
  obtain ⟨F, hF, hbound⟩ := finite_strip_cone_filtration_steps K r hsupport A a b hb f hf
  exact ⟨F, hF, hbound, finite_strip_cone_filtration_graded K r hsupport A a b hb f hf F hF⟩

end HomologicalComplex₂
