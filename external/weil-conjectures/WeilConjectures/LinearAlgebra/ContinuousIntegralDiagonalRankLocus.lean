/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Instances.Matrix

/-! # Local reduction near a fixed diagonal on its rank locus -/

@[expose] public section

universe u v

namespace Padic

open Topology Filter

private theorem continuous_cancel_uniformizer
    {A : Type u} [CommRing A] [IsDomain A] (π : A) (hπ : π ≠ 0)
    (T : Type v) [TopologicalSpace T] (q : T → A) (e : ℕ)
    (hq : @Continuous T A _ (Ideal.span {π}).adicTopology (fun t ↦ π ^ e * q t)) :
    @Continuous T A _ (Ideal.span {π}).adicTopology q := by
  let I : Ideal A := Ideal.span {π}
  let : TopologicalSpace A := I.adicTopology
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (I.hasBasis_nhds_adic (q t)).tendsto_right_iff.mpr
  intro k _
  have hh := ((I.hasBasis_nhds_adic (π ^ e * q t)).tendsto_right_iff.mp
    (hq.continuousAt)) (k + e) trivial
  apply hh.mono
  intro z hz
  obtain ⟨a, ha, hza⟩ := hz
  have ha' : π ^ (k + e) ∣ a := by
    change a ∈ I ^ (k + e) at ha
    dsimp only [I] at ha
    rw [Ideal.span_singleton_pow] at ha
    exact Ideal.mem_span_singleton.mp ha
  obtain ⟨b, hb⟩ := ha'
  refine ⟨π ^ k * b, ?_, ?_⟩
  · change π ^ k * b ∈ I ^ k
    dsimp only [I]
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  · apply mul_left_cancel₀ (pow_ne_zero e hπ)
    rw [mul_add, ← mul_assoc]
    rw [← hza, hb, pow_add]
    ring

private theorem clear_extra_columns
    {A : Type u} [CommRing A] [IsDomain A] {m n r : ℕ}
    (hr : r ≤ min m n) (d : Fin r → A)
    (D G : Matrix (Fin n) (Fin m) A)
    (hD : ∀ i j, D i j = if h : i.val = j.val ∧ i.val < r then d ⟨i.val, h.2⟩ else 0)
    (hc : ∀ i j, j.val < r → G i j = D i j)
    (q : Matrix (Fin m) (Fin m) A)
    (hq : ∀ i j, (if hi : i.val < r then d ⟨i.val, hi⟩ else 0) * q i j =
      if h : i.val < r ∧ r ≤ j.val then G (Fin.castLE (hr.trans (min_le_right _ _))
        ⟨i.val, h.1⟩) j else 0)
    (hz : ∀ i j, ¬(i.val < r ∧ r ≤ j.val) → q i j = 0) :
    ∃ R : Matrix.GeneralLinearGroup (Fin m) A,
      (R : Matrix (Fin m) (Fin m) A) = 1 - q ∧
      ((R⁻¹ : Matrix.GeneralLinearGroup (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1 + q ∧
      ∀ i j, i.val < r ∨ j.val < r → (G * (R : Matrix (Fin m) (Fin m) A)) i j = D i j := by
  classical
  have hqq : q * q = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < r
    · rw [hz i k (by omega), zero_mul]
    · rw [hz k j (by omega), mul_zero]
  let R : Matrix.GeneralLinearGroup (Fin m) A :=
    ⟨1 - q, 1 + q, by simp [mul_add, sub_mul, hqq], by
      simp [mul_sub, add_mul, hqq]⟩
  refine ⟨R, rfl, rfl, ?_⟩
  intro i j hij
  change (G * (1 - q : Matrix (Fin m) (Fin m) A)) i j = D i j
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]
  by_cases hj : j.val < r
  · have hGq : (G * q) i j = 0 := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [hz k j (by omega), mul_zero]
    rw [hGq, sub_zero]
    exact hc i j hj
  · have hi : i.val < r := hij.resolve_right hj
    have hm : r ≤ m := hr.trans (min_le_left _ _)
    let k : Fin m := ⟨i.val, by omega⟩
    have hGq : (G * q) i j = G i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single k]
      · have hk : k.val < r := hi
        rw [hc i k hk, hD, dite_eq_left (by exact ⟨rfl, hi⟩)]
        have hh := hq k j
        rw [dite_eq_left hk, dite_eq_left (by exact ⟨hk, by omega⟩)] at hh
        simpa only [k, Fin.castLE, Fin.eta] using hh
      · intro b _ hbk
        by_cases hb : b.val < r
        · rw [hc i b hb, hD, dite_eq_right, zero_mul]
          intro h
          exact hbk (Fin.ext h.1.symm)
        · rw [hz b j (by omega), mul_zero]
      · simp
    rw [hGq, sub_self, hD, dite_eq_right]
    intro h
    omega

private theorem continuous_matrix_unit_inverse
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsOpenUnits A] {T : Type v} [TopologicalSpace T] {n : ℕ}
    (M : T → Matrix (Fin n) (Fin n) A) (hM : Continuous M)
    (hu : ∀ t, IsUnit (M t).det) :
    Continuous (fun t ↦ (M t)⁻¹) := by
  let d : T → Aˣ := fun t ↦ (hu t).unit
  have hd : Continuous d :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.isInducing.continuous_iff.mpr
      (by simpa only [Function.comp_def, d, IsUnit.unit_spec] using hM.matrix_det)
  have hinv : Continuous (fun t ↦ (↑((d t)⁻¹) : A)) :=
    Units.continuous_coe_inv.comp hd
  have heq : (fun t ↦ (M t)⁻¹) = (fun t ↦ (↑((d t)⁻¹) : A) • (M t).adjugate) := by
    funext t
    exact Matrix.nonsing_inv_apply _ (hu t)
  rw [heq]
  exact hinv.smul hM.matrix_adjugate

private theorem diagonal_corner_eq {A : Type u} [CommRing A] [IsDomain A]
    {m n r : ℕ} (hr : r ≤ min m n) (d : Fin r → A) (hd : ∀ k, d k ≠ 0)
    (G D : Matrix (Fin n) (Fin m) A)
    (hD : ∀ i j, D i j = if h : i.val = j.val ∧ i.val < r then d ⟨i.val, h.2⟩ else 0)
    (hcorner : ∀ i j, i.val < r ∨ j.val < r → G i j = D i j)
    (hrank : G.rank ≤ r) : G = D := by
  classical
  have hrn : r ≤ n := hr.trans (min_le_right _ _)
  have hrm : r ≤ m := hr.trans (min_le_left _ _)
  ext i j
  by_cases hc : i.val < r ∨ j.val < r
  · exact hcorner i j hc
  have hi : r ≤ i.val := by omega
  have hj : r ≤ j.val := by omega
  have hDz : D i j = 0 := by
    rw [hD, dite_eq_right]
    omega
  rw [hDz]
  by_contra hn
  let a : Fin (r + 1) → Fin n := Fin.lastCases i (Fin.castLE hrn)
  let b : Fin (r + 1) → Fin m := Fin.lastCases j (Fin.castLE hrm)
  let q : Fin (r + 1) → A := Fin.lastCases (G i j) d
  have hblock : G.submatrix a b = Matrix.diagonal q := by
    ext x y
    refine Fin.lastCases ?_ (fun x ↦ ?_) x <;>
      refine Fin.lastCases ?_ (fun y ↦ ?_) y
    · simp [a, b, q]
    · have hxy : (Fin.last r) ≠ y.castSucc := by
        intro he
        have := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc] at this
        omega
      rw [Matrix.diagonal_apply_ne _ hxy]
      simp only [Matrix.submatrix_apply, a, b, Fin.lastCases_last,
        Fin.lastCases_castSucc]
      change G i (Fin.castLE hrm y) = 0
      rw [hcorner _ _ (Or.inr y.isLt), hD, dite_eq_right]
      simp only [Fin.val_castLE]
      omega
    · have hxy : x.castSucc ≠ Fin.last r := by
        intro he
        have := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc] at this
        omega
      rw [Matrix.diagonal_apply_ne _ hxy]
      simp only [Matrix.submatrix_apply, a, b, Fin.lastCases_last,
        Fin.lastCases_castSucc]
      change G (Fin.castLE hrn x) j = 0
      rw [hcorner _ _ (Or.inl x.isLt), hD, dite_eq_right]
      simp only [Fin.val_castLE]
      omega
    · simp only [Matrix.submatrix_apply, a, b, Fin.lastCases_castSucc]
      rw [hcorner _ _ (Or.inl x.isLt), hD]
      by_cases hxy : x = y
      · subst y
        simp [q]
      · have hval : x.val ≠ y.val := fun h ↦ hxy (Fin.ext h)
        simp [Matrix.diagonal, hxy, hval]
  have hdet : (G.submatrix a b).det ≠ 0 := by
    rw [hblock, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro x _
    refine Fin.lastCases ?_ (fun k ↦ ?_) x
    · simpa [q] using hn
    · simpa [q] using hd k
  have hh := Matrix.rank_submatrix_le G a b
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hh
  omega

private theorem diagonal_rank_locus_generic
    {A : Type u} [CommRing A] [IsDomain A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsOpenUnits A]
    (I : Ideal A) (htop : ‹TopologicalSpace A› = I.adicTopology) (π : A) (hπ0 : π ≠ 0)
    (hπ : Ideal.span ({π} : Set A) = I)
    (T : Type v) [TopologicalSpace T] (m n r : ℕ) (hr : r ≤ min m n)
    (e : Fin r → ℕ) (_he : Monotone e)
    (D : Matrix (Fin n) (Fin m) A)
    (hD : ∀ (i : Fin n) (j : Fin m),
      D i j = if h : i.val = j.val ∧ i.val < r then π ^ e ⟨i.val, h.2⟩ else 0)
    (F : T → Matrix (Fin n) (Fin m) A)
    (hF : ∀ (i : Fin n) (j : Fin m),
      Continuous (fun t ↦ F t i j))
    (t₀ : T) (hcenter : F t₀ = D) (hrank : ∀ t, (F t).rank ≤ r) :
    ∃ U : TopologicalSpace.Opens T, t₀ ∈ U ∧
      ∃ (L : U → Matrix.GeneralLinearGroup (Fin n) A)
        (R : U → Matrix.GeneralLinearGroup (Fin m) A),
        (∀ i j : Fin n,
          Continuous (fun t ↦ L t i j)) ∧
        (∀ i j : Fin n,
          Continuous (fun t ↦ (L t)⁻¹ i j)) ∧
        (∀ i j : Fin m,
          Continuous (fun t ↦ R t i j)) ∧
        (∀ i j : Fin m,
          Continuous (fun t ↦ (R t)⁻¹ i j)) ∧
        ∀ t : U,
          (L t : Matrix (Fin n) (Fin n) A) * F t.val *
            (R t : Matrix (Fin m) (Fin m) A) = D := by
  classical
  have hcancel {S : Type v} [TopologicalSpace S] (q : S → A) (k : ℕ)
      (hq : Continuous (fun t ↦ π ^ k * q t)) : Continuous q := by
    rw [htop, ← hπ] at *
    exact continuous_cancel_uniformizer π hπ0 S q k hq
  have hrm : r ≤ m := hr.trans (min_le_left _ _)
  have hrn : r ≤ n := hr.trans (min_le_right _ _)
  let N : ℕ := Finset.univ.sup e
  have heN (k : Fin r) : e k ≤ N := Finset.le_sup (Finset.mem_univ k)
  let V : TopologicalSpace.Opens T :=
    ⟨{t | ∀ i j, F t i j - D i j ∈ I ^ N}, by
      simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      have hcont : Continuous (fun t : T ↦ F t i j - D i j) := by
        exact (hF i j).sub (continuous_const : Continuous (fun _ : T ↦ D i j))
      have hopen : IsOpen ((I ^ N : Ideal A) : Set A) := (isAdic_iff.mp htop).1 N
      exact hopen.preimage hcont⟩
  have htV : t₀ ∈ V := by
    intro i j
    rw [hcenter, sub_self]
    exact Ideal.zero_mem _
  have hdiv (t : V) (i : Fin n) (j : Fin m) (k : Fin r) :
      π ^ e k ∣ F t.val i j - D i j := by
    apply Ideal.mem_span_singleton.mp
    rw [← Ideal.span_singleton_pow, hπ]
    exact Ideal.pow_le_pow_right (heN k) (t.property i j)
  choose Q hQ using fun (t : V) (i : Fin n) (k : Fin r) ↦
    hdiv t i (Fin.castLE hrm k) k
  have hQc (i : Fin n) (k : Fin r) : Continuous (fun t : V ↦ Q t i k) := by
    apply hcancel (fun t ↦ Q t i k) (e k)
    exact Continuous.congr
      (((hF i (Fin.castLE hrm k)).comp continuous_subtype_val).sub
        (continuous_const : Continuous (fun _ : V ↦ D i (Fin.castLE hrm k))))
      (fun t ↦ hQ t i k)
  let B : V → Matrix (Fin n) (Fin n) A := fun t i j ↦
    if hj : j.val < r then Q t i ⟨j.val, hj⟩ else 0
  have hBc : Continuous B := continuous_matrix fun i j ↦ by
    dsimp only [B]
    split_ifs with hj
    · exact hQc i ⟨j.val, hj⟩
    · exact continuous_const
  let M : V → Matrix (Fin n) (Fin n) A := fun t ↦ 1 + B t
  have hMc : Continuous M := continuous_const.add hBc
  have hM0 : M ⟨t₀, htV⟩ = 1 := by
    suffices hB0 : B ⟨t₀, htV⟩ = 0 by simp [M, hB0]
    ext i j
    dsimp only [B]
    split_ifs with hj
    · have hh := hQ (⟨t₀, htV⟩ : V) i ⟨j.val, hj⟩
      rw [hcenter, sub_self] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hπ0)
    · rfl
  let S : Set V := {t | IsUnit (M t).det}
  have hS : IsOpen S := by
    have hu : IsOpen {a : A | IsUnit a} := by
      convert (IsOpenUnits.isOpenEmbedding_unitsVal (M := A)).isOpen_range using 1
      ext a
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isUnit
    exact hu.preimage hMc.matrix_det
  let U₀ : TopologicalSpace.Opens V := ⟨S, hS⟩
  have htU₀ : (⟨t₀, htV⟩ : V) ∈ U₀ := by
    change IsUnit (M ⟨t₀, htV⟩).det
    rw [hM0, Matrix.det_one]
    exact isUnit_one
  let P : U₀ → Matrix.GeneralLinearGroup (Fin n) A := fun t ↦
    ((Matrix.isUnit_iff_isUnit_det (M t.val)).mpr t.property).unit
  have hP (t : U₀) : (P t : Matrix (Fin n) (Fin n) A) = M t.val := IsUnit.unit_spec _
  have hPc : Continuous (fun t : U₀ ↦ (P t : Matrix (Fin n) (Fin n) A)) := by
    simp_rw [hP]
    exact hMc.comp continuous_subtype_val
  have hPi (t : U₀) : ((P t)⁻¹).val = (M t.val)⁻¹ := by
    rw [← hP, Matrix.coe_units_inv]
  have hPic : Continuous (fun t : U₀ ↦ ((P t)⁻¹).val) := by
    simpa only [hPi] using continuous_matrix_unit_inverse
      (fun t : U₀ ↦ M t.val) (hMc.comp continuous_subtype_val) (fun t ↦ t.property)
  have hMD (t : V) (i : Fin n) (j : Fin m) (hj : j.val < r) :
      (M t * D) i j = F t.val i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hrn ⟨j.val, hj⟩)]
    · rw [hD, dite_eq_left ⟨rfl, hj⟩]
      change (1 + B t) i (Fin.castLE hrn ⟨j.val, hj⟩) * π ^ e ⟨j.val, hj⟩ = _
      rw [Matrix.add_apply, add_mul, Matrix.one_apply]
      dsimp only [B, Fin.val_castLE]
      rw [dite_eq_left hj]
      have hh : F t.val i j - D i j =
          π ^ e ⟨j.val, hj⟩ * Q t i ⟨j.val, hj⟩ := hQ t i ⟨j.val, hj⟩
      rw [hD] at hh
      by_cases hij : i.val = j.val
      · have hi : i = Fin.castLE hrn ⟨j.val, hj⟩ := Fin.ext hij
        subst i
        dsimp only [Fin.val_castLE] at hh ⊢
        rw [dite_eq_left ⟨rfl, hj⟩] at hh
        rw [ite_eq_left rfl, one_mul]
        linear_combination -hh
      · have hi : i ≠ Fin.castLE hrn ⟨j.val, hj⟩ := fun h ↦ hij (congrArg Fin.val h)
        rw [ite_eq_right hi, zero_mul, zero_add]
        rw [dite_eq_right (by intro h; exact hij h.1), sub_zero] at hh
        rw [mul_comm]
        exact hh.symm
    · intro b _ hb
      rw [hD, dite_eq_right, mul_zero]
      intro h
      exact hb (Fin.ext h.1)
    · simp
  let G : U₀ → Matrix (Fin n) (Fin m) A := fun t ↦
    ((P t)⁻¹).val * F t.val.val
  have hGc : Continuous G := hPic.matrix_mul
    ((continuous_matrix hF).comp (continuous_subtype_val.comp continuous_subtype_val))
  have hGcol (t : U₀) (i : Fin n) (j : Fin m) (hj : j.val < r) : G t i j = D i j := by
    calc
      G t i j = (((P t)⁻¹).val * (M t.val * D)) i j := by
        simp only [G, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _
        change ((P t)⁻¹).val i k * F t.val.val k j =
          ((P t)⁻¹).val i k * (M t.val * D) k j
        rw [hMD t.val k j hj]
      _ = D i j := by rw [← hP, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
  have hGdiv (t : U₀) (i : Fin n) (j : Fin m) (hj : r ≤ j.val) (k : Fin r) :
      π ^ e k ∣ G t i j := by
    dsimp only [G]
    rw [Matrix.mul_apply]
    apply Finset.dvd_sum
    intro b _
    apply dvd_mul_of_dvd_right
    have hDj : D b j = 0 := by rw [hD, dite_eq_right]; omega
    simpa only [hDj, sub_zero] using hdiv t.val b j k
  choose C hC using fun (t : U₀) (i : Fin r) (j : Fin m) (hj : r ≤ j.val) ↦
    hGdiv t (Fin.castLE hrn i) j hj i
  have hCc (i : Fin r) (j : Fin m) (hj : r ≤ j.val) :
      Continuous (fun t : U₀ ↦ C t i j hj) := by
    apply hcancel (fun t ↦ C t i j hj) (e i)
    apply Continuous.congr (hGc.matrix_elem (Fin.castLE hrn i) j)
    intro t
    exact hC t i j hj
  let q : U₀ → Matrix (Fin m) (Fin m) A := fun t i j ↦
    if h : i.val < r ∧ r ≤ j.val then C t ⟨i.val, h.1⟩ j h.2 else 0
  have hqc : Continuous q := continuous_matrix fun i j ↦ by
    dsimp only [q]
    split_ifs with h
    · exact hCc ⟨i.val, h.1⟩ j h.2
    · exact continuous_const
  have hq (t : U₀) : ∃ R : Matrix.GeneralLinearGroup (Fin m) A,
      (R : Matrix (Fin m) (Fin m) A) = 1 - q t ∧
      ((R⁻¹ : Matrix.GeneralLinearGroup (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1 + q t ∧
      ∀ i j, i.val < r ∨ j.val < r → (G t * (R : Matrix (Fin m) (Fin m) A)) i j = D i j := by
    apply clear_extra_columns hr (fun k ↦ π ^ e k) D (G t) hD (hGcol t) (q t)
    · intro i j
      by_cases h : i.val < r ∧ r ≤ j.val
      · simp only [q, dite_eq_left h, dite_eq_left h.1]
        exact (hC t ⟨i.val, h.1⟩ j h.2).symm
      · simp only [q, dite_eq_right h, mul_zero]
    · intro i j h
      exact dite_eq_right h
  choose R hR hRi hred using hq
  let U : TopologicalSpace.Opens T :=
    ⟨Subtype.val '' (U₀ : Set V), V.isOpen.isOpenMap_subtype_val _ U₀.isOpen⟩
  have hmem (t : U) : t.val ∈ V ∧ (⟨t.val, by
      obtain ⟨w, _, hw⟩ := t.property
      exact hw ▸ w.property⟩ : V) ∈ U₀ := by
    obtain ⟨w, hwU, hw⟩ := t.property
    refine ⟨by simpa only [← hw] using w.property, ?_⟩
    have heq : w = (⟨t.val, by simpa only [← hw] using w.property⟩ : V) :=
      Subtype.ext hw
    exact heq ▸ hwU
  let k : U → U₀ := fun t ↦ ⟨⟨t.val, (hmem t).1⟩, (hmem t).2⟩
  have hk : Continuous k := (continuous_subtype_val.subtype_mk _).subtype_mk _
  refine ⟨U, ⟨⟨t₀, htV⟩, htU₀, rfl⟩, (fun t ↦ (P (k t))⁻¹), (fun t ↦ R (k t)),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j ↦ (hPic.comp hk).matrix_elem i j
  · intro i j
    simp only [inv_inv]
    exact (hPc.matrix_elem i j).comp hk
  · intro i j
    have hh : Continuous (fun t : U₀ ↦ (R t : Matrix (Fin m) (Fin m) A)) := by
      simp_rw [hR]
      exact (continuous_const : Continuous (fun _ : U₀ ↦
        (1 : Matrix (Fin m) (Fin m) A))).sub hqc
    exact (hh.comp hk).matrix_elem i j
  · intro i j
    have hh : Continuous (fun t : U₀ ↦ ((R t)⁻¹).val) := by
      simp_rw [hRi]
      exact (continuous_const : Continuous (fun _ : U₀ ↦
        (1 : Matrix (Fin m) (Fin m) A))).add hqc
    exact (hh.comp hk).matrix_elem i j
  · intro t
    apply diagonal_corner_eq hr (fun k ↦ π ^ e k) (fun k ↦ pow_ne_zero _ hπ0)
      _ D hD (hred (k t))
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (hrank t.val))

/-- Near a specified Smith diagonal, a continuous matrix of rank at most its number
of nonzero diagonal entries is continuously equivalent to that same diagonal.

Source: Hemo--Richarz--Scholbach, proof of Theorem 6.12(2), finite extension case,
continuous integral division and pivot argument; agent rank-locus variant.
(auxiliary; not a blueprint node)

Proof: On an open congruence neighbourhood, divide the error in pivot column k by
its nonzero diagonal entry to form B, extending by zero in the remaining columns.
Cancellation in principal-ideal neighbourhood bases proves that these quotients are
continuous. At the centre B=0, so M=1+B is invertible on an open neighbourhood;
its inverse is continuous by the determinant-adjugate formula. The first r columns
of G=M inverse times F are precisely those of D. Each extra column is divisible by
every pivot. Divide its first r entries by the corresponding pivots to form q,
supported at rows below r and columns at least r. Then q squared is zero, and
R=1-q, with inverse 1+q, clears those entries. Any nonzero remaining entry would
produce a nonzero diagonal minor of size r+1, contradicting the rank bound.
Thus G R=D. Transport the open neighbourhood to T. The same formulas include
zero rank, empty dimensions and unit pivots. -/
theorem continuous_integral_diagonal_rank_locus
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (π : coefficientExtensionIntegers l E)
    (hπ : Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (T : Type v) [TopologicalSpace T] (m n r : ℕ) (hr : r ≤ min m n)
    (e : Fin r → ℕ) (he : Monotone e)
    (D : Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E))
    (hD : ∀ (i : Fin n) (j : Fin m),
      D i j = if h : i.val = j.val ∧ i.val < r then π ^ e ⟨i.val, h.2⟩ else 0)
    (F : T → Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E))
    (hF : ∀ (i : Fin n) (j : Fin m),
      @Continuous T (coefficientExtensionIntegers l E) _
        (coefficientExtensionMaximalIdeal l E).adicTopology (fun t ↦ F t i j))
    (t₀ : T) (hcenter : F t₀ = D) (hrank : ∀ t, (F t).rank ≤ r) :
    ∃ U : TopologicalSpace.Opens T, t₀ ∈ U ∧
      ∃ (L : U → Matrix.GeneralLinearGroup (Fin n) (coefficientExtensionIntegers l E))
        (R : U → Matrix.GeneralLinearGroup (Fin m) (coefficientExtensionIntegers l E)),
        (∀ i j : Fin n,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun t ↦ L t i j)) ∧
        (∀ i j : Fin n,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun t ↦ (L t)⁻¹ i j)) ∧
        (∀ i j : Fin m,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun t ↦ R t i j)) ∧
        (∀ i j : Fin m,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionMaximalIdeal l E).adicTopology (fun t ↦ (R t)⁻¹ i j)) ∧
        ∀ t : U,
          (L t : Matrix (Fin n) (Fin n) (coefficientExtensionIntegers l E)) * F t.val *
            (R t : Matrix (Fin m) (Fin m) (coefficientExtensionIntegers l E)) = D := by
  classical
  let A := coefficientExtensionIntegers l E
  let I : Ideal A := coefficientExtensionMaximalIdeal l E
  let : TopologicalSpace A := I.adicTopology
  let : IsTopologicalRing A := I.ringFilterBasis.isTopologicalRing
  have hdata := (coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsLocalRing A := hdata.2.2.2.1
  have hmax : IsLocalRing.maximalIdeal A = I :=
    hdata.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal A)
  have hm0 : I ≠ ⊥ := by
    rcases hdata with ⟨_, _, _, _, _, _, _, _, _, hm0, _⟩
    exact hm0
  have hπ0 : π ≠ 0 := by
    intro h
    apply hm0
    change coefficientExtensionMaximalIdeal l E = ⊥
    rw [← hπ, h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  let : IsOpenUnits A := IsOpenUnits.of_isAdic rfl
    (hmax ▸ IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
  exact diagonal_rank_locus_generic I rfl π hπ0 hπ
    T m n r hr e he D hD F hF t₀ hcenter hrank

end Padic
