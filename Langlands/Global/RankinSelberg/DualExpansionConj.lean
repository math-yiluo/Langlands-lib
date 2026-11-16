import Langlands.Global.RankinSelberg.DualExpansionRadical

/-! # Conjugating the radical `Y_(n,m)` into the dual period group -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (sqZeroUnit sqZeroUnit_val ratVec ratVec_apply)

variable {F : Type u} [Field F] [NumberField F]

local instance dualConjSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualConjSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {m K : ℕ}

section Weyl

/-- The involution of `Fin (m + K + 1)` reversing `m, …, m + K`. -/
def wPerm (a : Fin (m + K + 1)) : Fin (m + K + 1) :=
  if h : (a : ℕ) < m then a else ⟨2 * m + K - a, by omega⟩

theorem wPerm_val (a : Fin (m + K + 1)) :
    (wPerm a : ℕ) = if (a : ℕ) < m then (a : ℕ) else 2 * m + K - a := by
  unfold wPerm
  split_ifs <;> rfl

theorem wPerm_wPerm (a : Fin (m + K + 1)) : wPerm (wPerm a) = a := by
  ext
  rw [wPerm_val, wPerm_val]
  split_ifs <;> omega

theorem wPerm_eq_iff (a b : Fin (m + K + 1)) : wPerm a = wPerm b ↔ a = b :=
  ⟨fun h => by rw [← wPerm_wPerm a, h, wPerm_wPerm], fun h => h ▸ rfl⟩

variable (R : Type*) [CommRing R]

/-- The permutation matrix of `wPerm`: `diag(I_m, w_(K+1))`. -/
def wMat : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R := fun a b => if wPerm a = b then 1 else 0

variable {R}

theorem wMat_mul_apply (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R) (a b : Fin (m + K + 1)) :
    (wMat (m := m) (K := K) R * M) a b = M (wPerm a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (wPerm a)]
  · simp [wMat]
  · intro c _ hc
    simp [wMat, Ne.symm hc]
  · simp

theorem mul_wMat_apply (M : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R) (a b : Fin (m + K + 1)) :
    (M * wMat (m := m) (K := K) R) a b = M a (wPerm b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (wPerm b)]
  · simp [wMat, wPerm_wPerm]
  · intro c _ hc
    have : wPerm c ≠ b := fun h => hc (by rw [← h, wPerm_wPerm])
    simp [wMat, this]
  · simp

variable (R) in
theorem wMat_mul_wMat : wMat (m := m) (K := K) R * wMat R = 1 := by
  ext a b
  rw [wMat_mul_apply]
  simp only [wMat, wPerm_wPerm, Matrix.one_apply]

variable (R) in
/-- `diag(I_m, w_(K+1))` as an invertible matrix. -/
def wGL : Matrix.GeneralLinearGroup (Fin (m + K + 1)) R :=
  ⟨wMat R, wMat R, wMat_mul_wMat R, wMat_mul_wMat R⟩

/-- The adelic point `diag(I_m, w_(K+1))`. -/
def wPoint : Points F (m + K + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).symm (wGL (Adeles F))

theorem pointMatrix_wPoint : pointMatrix F (wPoint (F := F) (m := m) (K := K)) = wMat (Adeles F) := by
  simp only [wPoint, pointMatrix, MulEquiv.apply_symm_apply]
  rfl

theorem wPoint_mul_wPoint : wPoint (F := F) (m := m) (K := K) * wPoint = 1 := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_wPoint, wMat_mul_wMat, pointMatrix_one]

theorem pointMatrix_wPoint_conj (g : Points F (m + K + 1)) (a b : Fin (m + K + 1)) :
    pointMatrix F (wPoint * g * wPoint) a b = pointMatrix F g (wPerm a) (wPerm b) := by
  rw [pointMatrix_mul, pointMatrix_mul, pointMatrix_wPoint, mul_wMat_apply, wMat_mul_apply]

theorem wPoint_mem_rationalSubgroup :
    wPoint (F := F) (m := m) (K := K) ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (m + K + 1)) := by
  refine ⟨(GeneralLinearGroupPoints.rationalEquiv F (m + K + 1)).symm (wGL F), ?_⟩
  apply (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).injective
  rw [GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply, wPoint,
    MulEquiv.apply_symm_apply]
  ext a b
  rw [AdelicGL.rational_apply]
  simp only [wGL, wMat]
  split_ifs <;> simp

end Weyl

section Iota

theorem pointMatrix_iota {n : ℕ} (g : Points F n) (a b : Fin n) :
    pointMatrix F (iota F n g) a b = pointMatrix F g⁻¹ b a := by
  simp only [pointMatrix, UnequalAnalytic.adelicEquiv_iota, map_inv]
  rfl

theorem yPoint_inv (A : Fin (m + 1) × Fin K → Adeles F) : (yPoint A)⁻¹ = yPoint (-A) := by
  refine (inv_eq_of_mul_eq_one_right ?_)
  rw [yPoint_mul, add_neg_cancel, yPoint_zero]

theorem brPoint_inv (u : Points F K) : (brPoint (m := m) u)⁻¹ = brPoint u⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_)
  rw [← brPoint_mul, mul_inv_cancel, brPoint_one]

end Iota

section Conjugation

/-- The rectangle `X` of the conjugate of `y(A)`: `X(i, j) = -A(j, K-1-i)`. -/
def rectX (A : Fin (m + 1) × Fin K → Adeles F) : Fin K × Fin m → Adeles F :=
  fun p => -A (⟨p.2, by omega⟩, ⟨K - 1 - p.1, by omega⟩)

/-- The column `c` of the conjugate of `y(A)`: `c(i) = -A(m, K-1-i)`. -/
def rectC (A : Fin (m + 1) × Fin K → Adeles F) : Fin K → Adeles F :=
  fun i => -A (⟨m, by omega⟩, ⟨K - 1 - i, by omega⟩)

theorem wPoint_iota_yPoint (A : Fin (m + 1) × Fin K → Adeles F) :
    wPoint * iota F (m + K + 1) (yPoint A) * wPoint = xcPoint F (rectX A) (rectC A) := by
  apply point_ext
  ext a b
  rw [pointMatrix_wPoint_conj, pointMatrix_iota, yPoint_inv, pointMatrix_yPoint, pointMatrix_xcPoint]
  simp only [Matrix.add_apply, yMat, xcMat]
  rw [Matrix.one_apply, Matrix.one_apply]
  simp only [wPerm_eq_iff]
  by_cases ha : m ≤ (a : ℕ) ∧ (a : ℕ) < m + K
  · have hwa : (wPerm a : ℕ) = 2 * m + K - a := by rw [wPerm_val, ite_eq_right (by omega)]
    rw [dite_eq_left ha]
    by_cases hb : (b : ℕ) < m
    · have hwb : (wPerm b : ℕ) = b := by rw [wPerm_val, ite_eq_left hb]
      have hab : a ≠ b := fun h => by subst h; omega
      rw [dite_eq_left hb, dite_eq_left (show (wPerm b : ℕ) ≤ m ∧ m + 1 ≤ (wPerm a : ℕ) by omega),
        ite_eq_right (Ne.symm hab), ite_eq_right hab, zero_add, zero_add]
      simp only [Pi.neg_apply, rectX]
      congr 2
      ext
      · simp [hwb]
      · simp only [hwa]
        omega
    · by_cases hb2 : (b : ℕ) = m + K
      · have hwb : (wPerm b : ℕ) = m := by rw [wPerm_val, ite_eq_right hb]; omega
        have hab : a ≠ b := fun h => by subst h; omega
        rw [dite_eq_right hb, ite_eq_left hb2,
          dite_eq_left (show (wPerm b : ℕ) ≤ m ∧ m + 1 ≤ (wPerm a : ℕ) by omega),
          ite_eq_right (Ne.symm hab), ite_eq_right hab, zero_add, zero_add]
        simp only [Pi.neg_apply, rectC]
        congr 2
        ext
        · simp [hwb]
        · simp only [hwa]
          omega
      · have hwb : m + 1 ≤ (wPerm b : ℕ) := by rw [wPerm_val, ite_eq_right hb]; omega
        rw [dite_eq_right hb, ite_eq_right hb2, dite_eq_right (fun h => by omega), add_zero, add_zero]
        by_cases hab : a = b
        · rw [ite_eq_left hab.symm, ite_eq_left hab]
        · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab]
  · have hwa : ¬ (m + 1 ≤ (wPerm a : ℕ)) := by rw [wPerm_val]; split_ifs <;> omega
    rw [dite_eq_right ha, dite_eq_right (fun h => hwa h.2), add_zero, add_zero]
    by_cases hab : a = b
    · rw [ite_eq_left hab.symm, ite_eq_left hab]
    · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab]

theorem pointMatrix_dualConj (u : Points F K) (i j : Fin K) :
    pointMatrix F (dualConj F K u) i j = pointMatrix F u⁻¹ j.rev i.rev := by
  simp only [pointMatrix, adelicEquiv_dualConj, map_inv]
  exact dualConjGL_entry K (Adeles F) _ i j

theorem wPoint_iota_brPoint (u : Points F K) :
    wPoint * iota F (m + K + 1) (brPoint (m := m) u) * wPoint = midPoint F (dualConj F K u) := by
  apply point_ext
  ext a b
  rw [pointMatrix_wPoint_conj, pointMatrix_iota, brPoint_inv, pointMatrix_brPoint, brMat_apply,
    pointMatrix_midPoint]
  by_cases ha : m ≤ (a : ℕ) ∧ (a : ℕ) < m + K
  · have hwa : (wPerm a : ℕ) = 2 * m + K - a := by rw [wPerm_val, ite_eq_right (by omega)]
    by_cases hb : m ≤ (b : ℕ) ∧ (b : ℕ) < m + K
    · have hwb : (wPerm b : ℕ) = 2 * m + K - b := by rw [wPerm_val, ite_eq_right (by omega)]
      rw [dite_eq_left (show m + 1 ≤ (wPerm b : ℕ) by omega), dite_eq_left (show m + 1 ≤ (wPerm a : ℕ) by omega),
        dite_eq_left ⟨ha.1, ha.2, hb.1, hb.2⟩, pointMatrix_dualConj]
      congr 1
      · ext; simp [Fin.rev, hwb]; omega
      · ext; simp [Fin.rev, hwa]; omega
    · have hwb : (wPerm b : ℕ) ≤ m := by rw [wPerm_val]; split_ifs <;> omega
      have hab : a ≠ b := fun h => by subst h; exact hb ha
      have hwab : wPerm b ≠ wPerm a := fun h => hab ((wPerm_eq_iff _ _).mp h).symm
      rw [dite_eq_right (show ¬ m + 1 ≤ (wPerm b : ℕ) by omega), ite_eq_right hwab,
        dite_eq_right (fun h => hb ⟨h.2.2.1, h.2.2.2⟩), ite_eq_right hab]
  · have hwa : (wPerm a : ℕ) ≤ m := by rw [wPerm_val]; split_ifs <;> omega
    by_cases hb : m ≤ (b : ℕ) ∧ (b : ℕ) < m + K
    · have hwb : (wPerm b : ℕ) = 2 * m + K - b := by rw [wPerm_val, ite_eq_right (by omega)]
      have hab : a ≠ b := fun h => by subst h; exact ha hb
      rw [dite_eq_left (show m + 1 ≤ (wPerm b : ℕ) by omega),
        dite_eq_right (show ¬ m + 1 ≤ (wPerm a : ℕ) by omega),
        dite_eq_right (fun h => ha ⟨h.1, h.2.1⟩), ite_eq_right hab]
    · have hwb : (wPerm b : ℕ) ≤ m := by rw [wPerm_val]; split_ifs <;> omega
      rw [dite_eq_right (show ¬ m + 1 ≤ (wPerm b : ℕ) by omega), dite_eq_right (fun h => ha ⟨h.1, h.2.1⟩)]
      simp only [wPerm_eq_iff]
      by_cases hab : a = b
      · rw [ite_eq_left hab.symm, ite_eq_left hab]
      · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab]

/-- **The conjugation of the radical into the dual period group**:
`w ι(y(A) diag(I, u)) w = x̂(X) ĉ(c) · diag(I_m, dualConj u, 1)`. -/
theorem wPoint_iota_conj (A : Fin (m + 1) × Fin K → Adeles F) (u : Points F K) :
    wPoint * iota F (m + K + 1) (yPoint A * brPoint u) * wPoint =
      xcPoint F (rectX A) (rectC A) * midPoint F (dualConj F K u) := by
  rw [← wPoint_iota_yPoint, ← wPoint_iota_brPoint, UnequalAnalytic.iota_mul]
  simp only [mul_assoc]
  rw [← mul_assoc wPoint wPoint, wPoint_mul_wPoint, one_mul]

end Conjugation

section Character

theorem sum_superdiag_brMat {R : Type*} [CommRing R] (U : Matrix (Fin K) (Fin K) R) :
    ∑ i : Fin (m + K), brMat m K U i.castSucc i.succ =
      ∑ j : Fin K, if h : (j : ℕ) + 1 < K then U j ⟨(j : ℕ) + 1, h⟩ else 0 := by
  have hlow : ∀ i : Fin (m + K), brMat m K U i.castSucc i.succ ≠ 0 → m + 1 ≤ (i : ℕ) := by
    intro i hi
    by_contra hlt
    apply hi
    rw [brMat_apply, dite_eq_right (show ¬ (m + 1 ≤ ((i.castSucc : Fin (m + K + 1)) : ℕ)) by
      simp only [Fin.val_castSucc]; omega)]
    rw [ite_eq_right (fun h => by have := congrArg Fin.val h; simp at this)]
  refine Finset.sum_bij_ne_zero
    (fun i _ hi => (⟨(i : ℕ) - (m + 1), by have := hlow i hi; omega⟩ : Fin K))
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro i₁ _ h₁ i₂ _ h₂ heq
    have e := congrArg Fin.val heq
    simp only at e
    have := hlow i₁ h₁
    have := hlow i₂ h₂
    ext
    omega
  · intro j _ hj
    have hjK : (j : ℕ) + 1 < K := by
      by_contra h
      exact hj (by rw [dite_eq_right h])
    refine ⟨⟨m + 1 + j, by omega⟩, Finset.mem_univ _, ?_, ?_⟩
    · rw [brMat_apply, dite_eq_left (by simp), dite_eq_left (by simp; omega)]
      rw [dite_eq_left hjK] at hj
      convert hj using 2
      all_goals ext; first | (simp; done) | (simp; omega)
    · ext
      simp
  · intro i _ hi
    have hm := hlow i hi
    rw [brMat_apply, dite_eq_left (by simp; omega), dite_eq_left (by simp; omega),
      dite_eq_left (by simp; omega)]
    congr 1; ext; simp; omega

theorem superSum_eq_sum_superdiag {k : ℕ} (u : Points F (k + 1)) :
    superSum F u = ∑ i : Fin k, pointMatrix F u i.castSucc i.succ := by
  unfold superSum
  rw [Fin.sum_univ_castSucc, dite_eq_right (by simp), add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dite_eq_left (by simp)]
  rfl

theorem superSum_dualConj (u : unipotentAdelic F K) :
    superSum F (dualConj F K (u : Points F K)) = -superSum F (u : Points F K) := by
  cases K with
  | zero => simp [superSum]
  | succ k =>
    rw [superSum_eq_sum_superdiag, superSum_eq_sum_superdiag]
    simp only [pointMatrix, adelicEquiv_dualConj]
    refine sum_superdiag_dualConjGL (Adeles F) _ (isUnitriangular_of_mem_unipotentAdelic F u) ?_
    rw [← map_inv]
    exact isUnitriangular_of_mem_unipotentAdelic F u⁻¹

variable {ψ : AddChar (Adeles F) ℂ} (hψ1 : ∀ x, ‖ψ x‖ = 1)
include hψ1

theorem conj_projectionCharacter_brHom (u : unipotentAdelic F K) :
    starRingEnd ℂ (projectionCharacter F (m + K) m ψ (brHom F m K u)) =
      ψ (superSum F (dualConj F K (u : Points F K))) := by
  rw [projectionCharacter, conj_addChar_eq F ψ hψ1, superSum_dualConj]
  congr 1
  rw [neg_inj]
  change ∑ i : Fin (m + K), pointMatrix F (brPoint (m := m) (u : Points F K)) i.castSucc i.succ = _
  rw [pointMatrix_brPoint, sum_superdiag_brMat]
  rfl

theorem conj_projectionCharacter_yHom (A : Fin (m + 1) × Fin K → Adeles F) :
    starRingEnd ℂ (projectionCharacter F (m + K) m ψ (yHom F m K (Multiplicative.ofAdd A))) =
      ψ (lastEntry (rectC A)) := by
  rw [projectionCharacter, conj_addChar_eq F ψ hψ1]
  congr 1
  change -∑ i : Fin (m + K), pointMatrix F (yPoint (Multiplicative.toAdd
    (Multiplicative.ofAdd A))) i.castSucc i.succ = _
  rw [toAdd_ofAdd, pointMatrix_yPoint]
  simp only [Matrix.add_apply]
  cases K with
  | zero =>
    rw [Finset.sum_eq_zero]
    · simp [lastEntry]
    · intro i _
      rw [Matrix.one_apply_ne (fun h => by have := congrArg Fin.val h; simp at this)]
      simp only [yMat, zero_add]
      rw [dite_eq_right (fun h => by have := i.isLt; simp at h; omega)]
  | succ k =>
    rw [lastEntry_succ, Finset.sum_eq_single (⟨m, by omega⟩ : Fin (m + (k + 1)))]
    · rw [Matrix.one_apply_ne (fun h => by have := congrArg Fin.val h; simp at this), zero_add]
      simp only [yMat, rectC]
      rw [dite_eq_left (by simp)]
      congr 2; ext <;> simp
    · intro i _ hi
      rw [Matrix.one_apply_ne (fun h => by have := congrArg Fin.val h; simp at this), zero_add]
      simp only [yMat]
      rw [dite_eq_right (fun h => hi (by ext; simp at h ⊢; omega))]
    · intro h; exact absurd (Finset.mem_univ _) h

end Character

end Langlands.Global.RankinSelbergGlobal.Unfolding
