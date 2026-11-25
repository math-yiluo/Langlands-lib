/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Data.Int.Interval
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The termwise dual of a bounded cochain complex

Let `C` be a preadditive monoidal category and `K` a cochain complex in `C` all of whose terms
have right duals. The *termwise dual* `K^∨` (`CochainComplex.rightDual`) has terms
`(K^∨)ⁿ = (K⁻ⁿ)ᘁ` and differential `(-1)ʲ • (d_K^{-j-1})ᘁ : (K^∨)ʲ⁻¹ ⟶ (K^∨)ʲ`.

If `K` is bounded, `K` and `K^∨` form an exact pairing for the tensor product of cochain
complexes (`CochainComplex.exactPairingRightDual`). The evaluation `K^∨ ⊗ K ⟶ 𝟙_` is given on
the summand `(K⁻ᵖ)ᘁ ⊗ Kᵖ` of degree `0` by the evaluation of `Kᵖ`, and the coevaluation
`𝟙_ ⟶ K ⊗ K^∨` is the finite sum of the coevaluations `𝟙_ C ⟶ Kᵖ ⊗ (Kᵖ)ᘁ`. The signs in the
differential of `K^∨` make both maps of complexes, and the zigzag identities hold summandwise.
In particular a bounded complex of dualizable objects is dualizable
(`CochainComplex.isDualizable_of_isStrictlyGE_of_isStrictlyLE`).

## Implementation notes

The summands of the tensor product `K ⊗ L` in degree `n` are indexed by pairs `(p, q)` with
`p + q = n`. To avoid transporting along equalities such as `-(-p) = p`, the components of the
evaluation and coevaluation (`CochainComplex.rightDual.evalPQ`, `CochainComplex.rightDual.coevPQ`)
are defined for all such pairs, using the isomorphisms `HomologicalComplex.XIsoOfEq`, and the
lemmas about them are proved for indices which are variables.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

section

variable {D : Type*} [Category* D] [Preadditive D] (K : CochainComplex D ℤ)
  (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

private lemma isZero_X_of_notMem (p : ℤ) (hp : p ∉ Finset.Icc a b) : IsZero (K.X p) := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with hp | hp
  · exact K.isZero_of_isStrictlyGE a p hp
  · exact K.isZero_of_isStrictlyLE b p hp

end

section

variable {D : Type*} [Category* D] [MonoidalCategory D]

private lemma zigzag_conj {A B : D} [HasRightDual A] (e : A ≅ B) (f : B ⟶ A) (hf : f = e.inv) :
    (λ_ B).inv ≫ (η_ A Aᘁ ≫ e.hom ▷ Aᘁ) ▷ B ≫ (α_ B Aᘁ B).hom ≫ B ◁ (Aᘁ ◁ f ≫ ε_ A Aᘁ) =
      (ρ_ B).inv := by
  subst hf
  let _ : ExactPairing B Aᘁ := exactPairingCongrLeft e.symm
  have h := ExactPairing.evaluation_coevaluation B Aᘁ
  change (η_ A Aᘁ ≫ e.hom ▷ Aᘁ) ▷ B ≫ _ ≫ B ◁ (Aᘁ ◁ e.inv ≫ ε_ A Aᘁ) = _ at h
  rw [h, Iso.inv_hom_id_assoc]

private lemma zigzag_conj' {A B : D} [HasRightDual A] (e : B ≅ A) (f : A ⟶ B) (hf : f = e.inv) :
    (ρ_ (Aᘁ)).inv ≫ Aᘁ ◁ (η_ A Aᘁ ≫ f ▷ Aᘁ) ≫ (α_ Aᘁ B Aᘁ).inv ≫
      (Aᘁ ◁ e.hom ≫ ε_ A Aᘁ) ▷ Aᘁ = (λ_ (Aᘁ)).inv := by
  subst hf
  let _ : ExactPairing B Aᘁ := exactPairingCongrLeft e
  have h := ExactPairing.coevaluation_evaluation B Aᘁ
  change Aᘁ ◁ (η_ A Aᘁ ≫ e.inv ▷ Aᘁ) ≫ _ ≫ (Aᘁ ◁ e.hom ≫ ε_ A Aᘁ) ▷ Aᘁ = _ at h
  rw [h, Iso.inv_hom_id_assoc]

end

private lemma units_smul_smul_add_self {M : Type*} [AddCommGroup M] (u v : ℤˣ) (x : M)
    (h : u * v = -1) : u • v • x + x = 0 := by
  rw [smul_smul, h, Units.neg_smul, one_smul, neg_add_cancel]

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

private lemma rightAdjointMate_zero {X Y : C} [HasRightDual X] [HasRightDual Y] :
    (0 : X ⟶ Y)ᘁ = 0 := by
  simp [rightAdjointMate]

private lemma units_smul_whiskerRight {X Y : C} (u : ℤˣ) (f : X ⟶ Y) (Z : C) :
    (u • f) ▷ Z = u • (f ▷ Z) := by
  rw [Units.smul_def, Units.smul_def]
  exact Functor.map_zsmul (tensorRight Z)

private lemma whiskerLeft_units_smul (X : C) {Y Z : C} (u : ℤˣ) (f : Y ⟶ Z) :
    X ◁ (u • f) = u • (X ◁ f) := by
  rw [Units.smul_def, Units.smul_def]
  exact Functor.map_zsmul (tensorLeft X)

variable (K : CochainComplex C ℤ) [∀ n, HasRightDual (K.X n)]

/-- The termwise right dual `K^∨` of a cochain complex `K`, with `(K^∨)ⁿ = (K⁻ⁿ)ᘁ` and
differential `(-1)ʲ • (d_K^{-j-1})ᘁ : (K^∨)ʲ⁻¹ ⟶ (K^∨)ʲ`. -/
noncomputable def rightDual : CochainComplex C ℤ where
  X n := (K.X (-n))ᘁ
  d i j := j.negOnePow • (K.d (-j) (-i))ᘁ
  shape i j h := by
    rw [K.shape (-j) (-i) (by simp at h ⊢; omega), rightAdjointMate_zero, smul_zero]
  d_comp_d' i j k _ _ := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, ← comp_rightAdjointMate, K.d_comp_d,
      rightAdjointMate_zero, smul_zero, smul_zero]

lemma rightDual_X (n : ℤ) : K.rightDual.X n = (K.X (-n))ᘁ := rfl


lemma rightDual_d (i j : ℤ) : K.rightDual.d i j = j.negOnePow • (K.d (-j) (-i))ᘁ := rfl

namespace rightDual

lemma isZero_X (n : ℤ) (hn : IsZero (K.X (-n))) : IsZero (K.rightDual.X n) := by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((K.X (-n))ᘁ) = 0
  rw [← rightAdjointMate_id, hn.eq_of_src (𝟙 _) 0, rightAdjointMate_zero]

/-- The evaluation `K^∨.X q ⊗ K.X p ⟶ 𝟙_ C` on a summand of degree `q + p = 0`. -/
noncomputable def evalPQ (q p : ℤ) (h : q + p = 0) : K.rightDual.X q ⊗ K.X p ⟶ 𝟙_ C :=
  K.rightDual.X q ◁ (K.XIsoOfEq (show p = -q by omega)).hom ≫ ε_ (K.X (-q)) (K.X (-q))ᘁ

lemma evalPQ_comm (q p : ℤ) (h : q + p + 1 = 0) :
    K.rightDual.d q (q + 1) ▷ K.X p ≫ evalPQ K (q + 1) p (by omega) +
      q.negOnePow • (K.rightDual.X q ◁ K.d p (p + 1) ≫ evalPQ K q (p + 1) (by omega)) = 0 := by
  obtain rfl : q = -p - 1 := by omega
  have hd : (K.XIsoOfEq (show p = -(-p - 1 + 1) by omega)).hom ≫ K.d (-(-p - 1 + 1)) (-(-p - 1)) =
      K.d p (p + 1) ≫ (K.XIsoOfEq (show p + 1 = -(-p - 1) by omega)).hom := by
    rw [HomologicalComplex.XIsoOfEq_hom_comp_d, HomologicalComplex.d_comp_XIsoOfEq_hom]
  have hs : (-p - 1 + 1).negOnePow = -(-p - 1).negOnePow := by
    rw [Int.negOnePow_succ]
  simp only [evalPQ, rightDual, hs]
  rw [units_smul_whiskerRight, Linear.units_smul_comp, ← whisker_exchange_assoc,
    rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc, hd, whiskerLeft_comp_assoc,
    Units.neg_smul]
  exact neg_add_cancel _

/-- The coevaluation `𝟙_ C ⟶ K.X p ⊗ K^∨.X q` on a summand of degree `p + q = 0`. -/
noncomputable def coevPQ (p q : ℤ) (h : p + q = 0) : 𝟙_ C ⟶ K.X p ⊗ K.rightDual.X q :=
  η_ (K.X (-q)) (K.X (-q))ᘁ ≫ (K.XIsoOfEq (show -q = p by omega)).hom ▷ (K.X (-q))ᘁ
end rightDual

section

variable [HasZeroObject C]

instance rightDual.isStrictlyGE (b : ℤ) [K.IsStrictlyLE b] : K.rightDual.IsStrictlyGE (-b) := by
  rw [isStrictlyGE_iff]
  exact fun n hn ↦ rightDual.isZero_X K n (K.isZero_of_isStrictlyLE b (-n) (by omega))

instance rightDual.isStrictlyLE (a : ℤ) [K.IsStrictlyGE a] : K.rightDual.IsStrictlyLE (-a) := by
  rw [isStrictlyLE_iff]
  exact fun n hn ↦ rightDual.isZero_X K n (K.isZero_of_isStrictlyGE a (-n) (by omega))

lemma rightDual.coevPQ_eq_zero (p q : ℤ) (h : p + q = 0) (hp : IsZero (K.X p)) :
    coevPQ K p q h = 0 :=
  (((curriedTensor C).map_isZero hp).obj _).eq_of_tgt _ _

end

variable [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace rightDual

/-- The evaluation `K^∨ ⊗ K ⟶ 𝟙_` of the termwise dual. -/
noncomputable def eval : K.rightDual ⊗ K ⟶ 𝟙_ (CochainComplex C ℤ) :=
  HomologicalComplex.mkHomToSingle
    (HomologicalComplex.mapBifunctorDesc (fun q p h ↦ evalPQ K q p h)) (by
      intro i hi
      have hi' : i + 1 = 0 := hi
      refine HomologicalComplex.mapBifunctor.hom_ext (fun q p h ↦ ?_)
      have h' : q + p = i := h
      rw [comp_zero, ← assoc]
      erw [ιTensorObj_d _ _ q p i 0 h' hi']
      rw [Preadditive.add_comp, assoc, Linear.units_smul_comp, assoc]
      erw [HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
      exact evalPQ_comm K q p (by omega))


/-- The differential of `K ⊗ K^∨` applied to `coevPQ`, first part. -/
noncomputable def coevD₁ (p q p₁ : ℤ) (h : p + q = 0) (hp : p + 1 = p₁) :
    𝟙_ C ⟶ (K ⊗ K.rightDual).X 1 :=
  coevPQ K p q h ≫ K.d p p₁ ▷ K.rightDual.X q ≫
    HomologicalComplex.ιTensorObj K K.rightDual p₁ q 1 (by omega)

/-- The differential of `K ⊗ K^∨` applied to `coevPQ`, second part. -/
noncomputable def coevD₂ (p q q₁ : ℤ) (h : p + q = 0) (hq : q + 1 = q₁) :
    𝟙_ C ⟶ (K ⊗ K.rightDual).X 1 :=
  p.negOnePow • (coevPQ K p q h ≫ K.X p ◁ K.rightDual.d q q₁ ≫
    HomologicalComplex.ιTensorObj K K.rightDual p q₁ 1 (by omega))

lemma coevD₁_congr (p q p₁ p' q' p₁' : ℤ) (h : p + q = 0) (hp : p + 1 = p₁)
    (h' : p' + q' = 0) (hp' : p' + 1 = p₁') (e : p = p') (e' : q = q') :
    coevD₁ K p q p₁ h hp = coevD₁ K p' q' p₁' h' hp' := by
  subst e e' hp hp'
  rfl

lemma coevD₂_add_coevD₁ (p q q₁ p' : ℤ) (h : p + q = 0) (hq : q + 1 = q₁)
    (hp' : p' + 1 = p) :
    coevD₂ K p q q₁ h hq + coevD₁ K p' q₁ p (by omega) hp' = 0 := by
  subst hq hp'
  obtain rfl : q = -p' - 1 := by omega
  have hd : K.d (-(-p' - 1 + 1)) (-(-p' - 1)) ≫
      (K.XIsoOfEq (show -(-p' - 1) = p' + 1 by omega)).hom =
      (K.XIsoOfEq (show -(-p' - 1 + 1) = p' by omega)).hom ≫ K.d p' (p' + 1) := by
    rw [HomologicalComplex.d_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_hom_comp_d]
  have hs : (p' + 1).negOnePow * (-p' - 1 + 1).negOnePow = -1 := by
    rw [← Int.negOnePow_add, show p' + 1 + (-p' - 1 + 1) = 1 by omega, Int.negOnePow_one]
  simp only [coevD₂, coevD₁, coevPQ, rightDual, whiskerLeft_units_smul, Linear.units_smul_comp,
    Linear.comp_units_smul, assoc]
  rw [← whisker_exchange_assoc, coevaluation_comp_rightAdjointMate_assoc,
    ← comp_whiskerRight_assoc, hd, comp_whiskerRight_assoc]
  exact units_smul_smul_add_self _ _ _ hs

variable (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

/-- The degree `0` component `𝟙_ C ⟶ (K ⊗ K^∨).X 0` of the coevaluation. -/
noncomputable def coevZero : 𝟙_ C ⟶ (K ⊗ K.rightDual).X 0 :=
  ∑ p ∈ Finset.Icc a b,
    coevPQ K p (-p) (by simp) ≫ HomologicalComplex.ιTensorObj K K.rightDual p (-p) 0 (by simp)

lemma coevZero_comp_d : coevZero K a b ≫ (K ⊗ K.rightDual).d 0 1 = 0 := by
  let f : ℤ → (𝟙_ C ⟶ (K ⊗ K.rightDual).X 1) := fun p ↦ coevD₁ K p (-p) (p + 1) (by simp) rfl
  have hf : ∀ p ∉ Finset.Icc a b, f p = 0 := fun p hp ↦ by
    simp only [f, coevD₁, coevPQ_eq_zero K p (-p) (by simp) (isZero_X_of_notMem K a b p hp),
      zero_comp]
  have hf' : ∀ p ∉ Finset.Icc a b, f (p - 1) = 0 := fun p hp ↦ by
    by_cases hp' : p - 1 ∈ Finset.Icc a b
    · obtain rfl : p = b + 1 := by simp only [Finset.mem_Icc] at hp hp'; omega
      simp only [f, coevD₁]
      rw [(K.isZero_of_isStrictlyLE b (b + 1 - 1 + 1) (by omega)).eq_of_tgt (K.d _ _) 0]
      simp
    · exact hf _ hp'
  have e : ∀ p : ℤ, coevPQ K p (-p) (by simp) ≫
      HomologicalComplex.ιTensorObj K K.rightDual p (-p) 0 (by simp) ≫
        (K ⊗ K.rightDual).d 0 1 = f p - f (p - 1) := fun p ↦ by
    erw [ιTensorObj_d K K.rightDual p (-p) 0 1 (by simp) rfl]
    have h := coevD₂_add_coevD₁ K p (-p) (-p + 1) (p - 1) (by simp) rfl (by omega)
    rw [coevD₁_congr K (p - 1) (-p + 1) p (p - 1) (-(p - 1)) (p - 1 + 1) (by omega) (by omega)
      (by simp) rfl rfl (by omega)] at h
    rw [sub_eq_add_neg, ← eq_neg_of_add_eq_zero_left h, Preadditive.comp_add,
      Linear.comp_units_smul]
    rfl
  simp only [coevZero, Preadditive.sum_comp, assoc, e, Finset.sum_sub_distrib]
  rw [← finsum_eq_sum_of_support_subset f (s := Finset.Icc a b) ?_,
    ← finsum_eq_sum_of_support_subset (fun p ↦ f (p - 1)) (s := Finset.Icc a b) ?_]
  · change _ - ∑ᶠ p, f (Equiv.subRight 1 p) = 0
    rw [finsum_comp_equiv (Equiv.subRight 1) (f := f), sub_self]
  · intro p hp
    by_contra hp'
    exact hp (hf' p hp')
  · intro p hp
    by_contra hp'
    exact hp (hf p hp')


/-- The coevaluation `𝟙_ ⟶ K ⊗ K^∨` of the termwise dual of a bounded complex. -/
noncomputable def coev : 𝟙_ (CochainComplex C ℤ) ⟶ K ⊗ K.rightDual :=
  HomologicalComplex.mkHomFromSingle (coevZero K a b) (by
    rintro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    exact coevZero_comp_d K a b)


lemma eval_f_eq_zero (k : ℤ) (hk : k ≠ 0) : (eval K).f k = 0 :=
  (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ C) k hk).eq_of_tgt _ _

lemma ι_eval_f (q p : ℤ) (h : q + p = 0) :
    HomologicalComplex.ιTensorObj K.rightDual K q p 0 h ≫ (eval K).f 0 =
      evalPQ K q p h ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv := by
  rw [eval, HomologicalComplex.mkHomToSingle_f]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]


end rightDual

section Unitors

variable (L : CochainComplex C ℤ)

lemma leftUnitor_inv_f (n : ℤ) :
    (λ_ L).inv.f n = (λ_ (L.X n)).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ▷ L.X n ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex C ℤ)) L 0 n n (zero_add n) :=
  HomologicalComplex.leftUnitor'_inv L n

lemma rightUnitor_inv_f (n : ℤ) :
    (ρ_ L).inv.f n = (ρ_ (L.X n)).inv ≫
      L.X n ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫
        HomologicalComplex.ιTensorObj L (𝟙_ (CochainComplex C ℤ)) n 0 n (add_zero n) :=
  HomologicalComplex.rightUnitor'_inv L n

end Unitors

namespace rightDual

variable (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

lemma singleObjXSelf_inv_coev_f :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫ (coev K a b).f 0 =
      coevZero K a b := by
  rw [coev, HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]

lemma evalCoev_term (p q k n : ℤ) (hpq : p + q = 0) (hk : q + n = k) (hpk : p + k = n) :
    (λ_ (K.X n)).inv ≫ coevPQ K p q hpq ▷ K.X n ≫ (α_ _ _ _).hom ≫
      K.X p ◁ (HomologicalComplex.ιTensorObj K.rightDual K q n k hk ≫ (eval K).f k) ≫
        HomologicalComplex.ιTensorObj K (𝟙_ (CochainComplex C ℤ)) p k n hpk =
      if p = n then (ρ_ K).inv.f n else 0 := by
  by_cases hk0 : k = 0
  · subst hk0
    obtain rfl : n = p := by omega
    rw [ite_eq_left rfl, rightUnitor_inv_f, ι_eval_f, whiskerLeft_comp]
    have hf : (K.XIsoOfEq (show n = -q by omega)).hom =
        (K.XIsoOfEq (show -q = n by omega)).inv := by
      rw [← cancel_epi (K.XIsoOfEq (show -q = n by omega)).hom, Iso.hom_inv_id,
        HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_rfl]
      rfl
    have key : (λ_ (K.X n)).inv ≫ coevPQ K n q hpq ▷ K.X n ≫ (α_ _ _ _).hom ≫
        K.X n ◁ evalPQ K q n hk = (ρ_ _).inv :=
      zigzag_conj (K.XIsoOfEq (show -q = n by omega)) _ hf
    simp only [assoc]
    rw [reassoc_of% key]
  · rw [ite_eq_right (by omega), eval_f_eq_zero K k hk0]
    simp

lemma coev_whiskerRight_comp :
    coev K a b ▷ K ≫ (α_ K K.rightDual K).hom ≫ K ◁ eval K = (λ_ K).hom ≫ (ρ_ K).inv := by
  ext n
  rw [← cancel_epi ((λ_ K).inv.f n)]
  conv_rhs => rw [← HomologicalComplex.comp_f, Iso.inv_hom_id_assoc]
  simp only [HomologicalComplex.comp_f]
  rw [leftUnitor_inv_f, assoc, assoc]
  erw [Monoidal.ι_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc, singleObjXSelf_inv_coev_f, coevZero, sum_whiskerRight,
    Preadditive.sum_comp, Preadditive.comp_sum]
  have h : ∀ p ∈ Finset.Icc a b, (λ_ (K.X n)).inv ≫
      (coevPQ K p (-p) (by simp) ≫
        HomologicalComplex.ιTensorObj K K.rightDual p (-p) 0 (by simp)) ▷ K.X n ≫
      HomologicalComplex.ιTensorObj (K ⊗ K.rightDual) K 0 n n (zero_add n) ≫
        (α_ K K.rightDual K).hom.f n ≫ (K ◁ eval K).f n =
      if p = n then (ρ_ K).inv.f n else 0 := fun p _ ↦ by
    rw [comp_whiskerRight, assoc,
      ← reassoc_of% (Monoidal.ι₁₂_eq K K.rightDual K p (-p) n 0 n (by simp) (zero_add n))]
    erw [Monoidal.ι₁₂_associator_hom_assoc]
    rw [Monoidal.ι₂₃_eq K K.rightDual K p (-p) n (-p + n) n rfl (by omega), assoc]
    erw [ιTensorObj_whiskerLeft_f]
    rw [← whiskerLeft_comp_assoc]
    exact evalCoev_term K p (-p) (-p + n) n (by simp) rfl (by omega)
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · exact (isZero_X_of_notMem K a b n hn).eq_of_src _ _

lemma coevEval_term (n p q k : ℤ) (hpq : p + q = 0) (hk : n + p = k) (hkq : k + q = n) :
    (ρ_ (K.rightDual.X n)).inv ≫ K.rightDual.X n ◁ coevPQ K p q hpq ≫ (α_ _ _ _).inv ≫
      (HomologicalComplex.ιTensorObj K.rightDual K n p k hk ≫ (eval K).f k) ▷ K.rightDual.X q ≫
        HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex C ℤ)) K.rightDual k q n hkq =
      if p = -n then (λ_ K.rightDual).inv.f n else 0 := by
  by_cases hk0 : k = 0
  · subst hk0
    obtain rfl : p = -n := by omega
    obtain rfl : n = q := by omega
    rw [ite_eq_left rfl, leftUnitor_inv_f, ι_eval_f, comp_whiskerRight]
    have hf : (K.XIsoOfEq (show -n = -n by omega)).hom =
        (K.XIsoOfEq (show -n = -n by omega)).inv := by
      rw [HomologicalComplex.XIsoOfEq_rfl]
      rfl
    have key : (ρ_ (K.rightDual.X n)).inv ≫ K.rightDual.X n ◁ coevPQ K (-n) n hpq ≫
        (α_ _ _ _).inv ≫ evalPQ K n (-n) hk ▷ K.rightDual.X n = (λ_ _).inv :=
      zigzag_conj' (K.XIsoOfEq (show -n = -n by omega)) _ hf
    simp only [assoc]
    rw [reassoc_of% key]
  · rw [ite_eq_right (by omega), eval_f_eq_zero K k hk0]
    simp

lemma whiskerLeft_coev_comp :
    K.rightDual ◁ coev K a b ≫ (α_ K.rightDual K K.rightDual).inv ≫ eval K ▷ K.rightDual =
      (ρ_ K.rightDual).hom ≫ (λ_ K.rightDual).inv := by
  ext n
  rw [← cancel_epi ((ρ_ K.rightDual).inv.f n)]
  conv_rhs => rw [← HomologicalComplex.comp_f, Iso.inv_hom_id_assoc]
  simp only [HomologicalComplex.comp_f]
  rw [rightUnitor_inv_f, assoc, assoc]
  erw [ιTensorObj_whiskerLeft_f_assoc]
  rw [← whiskerLeft_comp_assoc, singleObjXSelf_inv_coev_f, coevZero, whiskerLeft_sum,
    Preadditive.sum_comp, Preadditive.comp_sum]
  have h : ∀ p ∈ Finset.Icc a b, (ρ_ (K.rightDual.X n)).inv ≫
      K.rightDual.X n ◁ (coevPQ K p (-p) (by simp) ≫
        HomologicalComplex.ιTensorObj K K.rightDual p (-p) 0 (by simp)) ≫
      HomologicalComplex.ιTensorObj K.rightDual (K ⊗ K.rightDual) n 0 n (add_zero n) ≫
        (α_ K.rightDual K K.rightDual).inv.f n ≫ (eval K ▷ K.rightDual).f n =
      if p = -n then (λ_ K.rightDual).inv.f n else 0 := fun p _ ↦ by
    rw [whiskerLeft_comp, assoc,
      ← reassoc_of% (Monoidal.ι₂₃_eq K.rightDual K K.rightDual n p (-p) 0 n (by simp)
        (add_zero n))]
    erw [Monoidal.ι₂₃_associator_inv_assoc]
    rw [Monoidal.ι₁₂_eq K.rightDual K K.rightDual n p (-p) (n + p) n rfl (by omega), assoc]
    erw [Monoidal.ι_whiskerRight]
    rw [← comp_whiskerRight_assoc]
    exact coevEval_term K n p (-p) (n + p) (by simp) rfl (by omega)
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · exact (rightDual.isZero_X K n (isZero_X_of_notMem K a b (-n) hn)).eq_of_src _ _

end rightDual

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

/-- A bounded complex `K` whose terms have right duals is paired with its termwise right dual
`K^∨`, `(K^∨)ⁿ = (K⁻ⁿ)ᘁ`. -/
@[instance_reducible]
noncomputable def exactPairingRightDual : ExactPairing K K.rightDual where
  coevaluation' := rightDual.coev K a b
  evaluation' := rightDual.eval K
  coevaluation_evaluation' := rightDual.whiskerLeft_coev_comp K a b
  evaluation_coevaluation' := rightDual.coev_whiskerRight_comp K a b

omit [∀ n, HasRightDual (K.X n)] in
variable {K} in
include a b in
/-- A bounded cochain complex whose terms are dualizable is dualizable. -/
theorem isDualizable_of_isStrictlyGE_of_isStrictlyLE (hK : ∀ n, IsDualizable (K.X n)) :
    IsDualizable K := by
  let _ : ∀ n, HasRightDual (K.X n) := fun n ↦ (hK n).some
  exact ⟨{ rightDual := K.rightDual, exact := exactPairingRightDual K a b }⟩

end CochainComplex
