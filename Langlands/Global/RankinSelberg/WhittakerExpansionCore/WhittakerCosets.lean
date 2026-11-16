import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerFrequency

/-! # Coset representatives with a prescribed last row

For a nonzero row `ξ ∈ K^(k+1)` and an index `i` with `ξ_i ≠ 0`, the matrix `rowGL ξ i` has
last row `ξ` and its other rows are the standard basis vectors `e_b` (`b ≠ i`); its inverse is
explicit. Every coset `q ∈ N_(j+1)(F) \ GL_(j+1)(F)` is `N_(j+1)(F) diag(γ', 1) γ_ξ` with
`ξ` the last row of `q` and `γ_ξ = rowGL ξ i`, and `q ↦ (ξ, N_j(F) γ')` is injective. When
`M ξ` is integral for a positive integer `M`, the height of `γ_ξ` is polynomial in `M` and the
size of `M ξ`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints PrimitiveAdelicHeight

local instance cosetsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance cosetsSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section RowMatrix

variable {K : Type*} [Field K] {k : ℕ}

open scoped Classical

/-- The matrix with last row `ξ` whose row `a ≠ last` is `e_(σ a)`, `σ = (i last)`. -/
def rowMatrix (ξ : Fin (k + 1) → K) (i : Fin (k + 1)) : Matrix (Fin (k + 1)) (Fin (k + 1)) K :=
  Matrix.of fun a b => if a = Fin.last k then ξ b else
    if b = Equiv.swap i (Fin.last k) a then 1 else 0

/-- The inverse of `rowMatrix ξ i` when `ξ_i ≠ 0`. -/
def rowMatrixInv (ξ : Fin (k + 1) → K) (i : Fin (k + 1)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) K :=
  Matrix.of fun b a => if b = i then
      (if a = Fin.last k then (ξ i)⁻¹ else -(ξ (Equiv.swap i (Fin.last k) a) * (ξ i)⁻¹))
    else if a = Equiv.swap i (Fin.last k) b then 1 else 0

theorem swap_last_eq_iff (i a : Fin (k + 1)) :
    Equiv.swap i (Fin.last k) a = i ↔ a = Fin.last k := by
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

theorem rowMatrix_mul_rowMatrixInv {ξ : Fin (k + 1) → K} {i : Fin (k + 1)} (hi : ξ i ≠ 0) :
    rowMatrix ξ i * rowMatrixInv ξ i = 1 := by
  set σ := Equiv.swap i (Fin.last k) with hσ
  ext a c
  rw [Matrix.mul_apply]
  by_cases ha : a = Fin.last k
  · subst ha
    simp only [rowMatrix, rowMatrixInv, Matrix.of_apply, ite_true]
    by_cases hc : c = Fin.last k
    · subst hc
      rw [Fintype.sum_eq_single i]
      · rw [ite_eq_left rfl, ite_eq_left rfl, mul_inv_cancel₀ hi, Matrix.one_apply_eq]
      · intro b hb
        rw [ite_eq_right hb, ite_eq_right, mul_zero]
        intro h
        apply hb
        rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact h
    · have hne : i ≠ σ c := fun h => hc ((swap_last_eq_iff i c).mp h.symm)
      rw [Fintype.sum_eq_add i (σ c) hne]
      · rw [ite_eq_left rfl, ite_eq_right hc, ite_eq_right hne.symm, ite_eq_left (by rw [hσ, Equiv.swap_apply_self]),
          mul_one, Matrix.one_apply_ne (Ne.symm hc)]
        field_simp
        ring
      · intro b hb
        rw [ite_eq_right hb.1, ite_eq_right, mul_zero]
        intro h
        apply hb.2
        rw [h, hσ, Equiv.swap_apply_self]
  · simp only [rowMatrix, rowMatrixInv, Matrix.of_apply, ite_eq_right ha]
    have hσa : σ a ≠ i := fun h => ha ((swap_last_eq_iff i a).mp h)
    rw [Fintype.sum_eq_single (σ a)]
    · rw [ite_eq_left rfl, one_mul, ite_eq_right hσa, hσ, Equiv.swap_apply_self, Matrix.one_apply]
      by_cases hca : c = a
      · rw [ite_eq_left hca, ite_eq_left hca.symm]
      · rw [ite_eq_right hca, ite_eq_right (Ne.symm hca)]
    · intro b hb
      rw [ite_eq_right hb, zero_mul]

/-- `rowMatrix ξ i` as an invertible matrix. -/
def rowGL (ξ : Fin (k + 1) → K) (i : Fin (k + 1)) (hi : ξ i ≠ 0) :
    Matrix.GeneralLinearGroup (Fin (k + 1)) K where
  val := rowMatrix ξ i
  inv := rowMatrixInv ξ i
  val_inv := rowMatrix_mul_rowMatrixInv hi
  inv_val := mul_eq_one_comm.mp (rowMatrix_mul_rowMatrixInv hi)

theorem coe_rowGL {ξ : Fin (k + 1) → K} {i : Fin (k + 1)} (hi : ξ i ≠ 0) :
    ((rowGL ξ i hi : Matrix.GeneralLinearGroup (Fin (k + 1)) K) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) K) = rowMatrix ξ i := rfl

theorem coe_rowGL_inv {ξ : Fin (k + 1) → K} {i : Fin (k + 1)} (hi : ξ i ≠ 0) :
    (((rowGL ξ i hi)⁻¹ : Matrix.GeneralLinearGroup (Fin (k + 1)) K) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) K) = rowMatrixInv ξ i := rfl

theorem rowGL_last {ξ : Fin (k + 1) → K} {i : Fin (k + 1)} (hi : ξ i ≠ 0) (b : Fin (k + 1)) :
    ((rowGL ξ i hi : Matrix.GeneralLinearGroup (Fin (k + 1)) K) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Fin.last k) b = ξ b := by
  rw [coe_rowGL]
  simp [rowMatrix]

/-- An index with a nonzero entry (`0` for the zero row). -/
def rowPivot (ξ : Fin (k + 1) → K) : Fin (k + 1) :=
  if h : ∃ i, ξ i ≠ 0 then h.choose else 0

theorem rowPivot_spec {ξ : Fin (k + 1) → K} (hξ : ξ ≠ 0) : ξ (rowPivot ξ) ≠ 0 := by
  have h : ∃ i, ξ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ (funext h)
  rw [rowPivot, dite_eq_left h]
  exact h.choose_spec

/-- The last row of an invertible matrix is nonzero. -/
theorem lastRow_ne_zero (g : Matrix.GeneralLinearGroup (Fin (k + 1)) K) :
    (fun b => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Fin.last k) b) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun g.mul_inv (Fin.last k)) (Fin.last k)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have h2 : ∀ b, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Fin.last k) b = 0 :=
    fun b => congrFun h b
  simp only [h2, zero_mul, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

/-- Multiplying by the inverse of a matrix with the same last row gives a standard last row. -/
theorem lastRow_mul_inv_eq {g h : Matrix.GeneralLinearGroup (Fin (k + 1)) K}
    (hgh : ∀ b, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Fin.last k) b =
      (h : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Fin.last k) b) (b : Fin (k + 1)) :
    ((g * h⁻¹ : Matrix.GeneralLinearGroup (Fin (k + 1)) K) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Fin.last k) b =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Fin.last k) b := by
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [hgh]
  rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end RowMatrix

section Cosets

variable (F : Type u) [Field F] [NumberField F] {j : ℕ}

/-- The last row of a coset `N_(j+1)(F) g`, read on the chosen representative. -/
def cosetRow (q : UnipotentRationalCosets F (j + 1)) : Fin (j + 1) → F := fun b =>
  (q.out : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b

omit [NumberField F] in
theorem cosetRow_ne_zero (q : UnipotentRationalCosets F (j + 1)) : cosetRow F q ≠ 0 :=
  lastRow_ne_zero q.out

/-- The representative `γ_ξ` attached to the last row `ξ` of `q`. -/
def cosetGamma (q : UnipotentRationalCosets F (j + 1)) : RationalGL F (j + 1) :=
  rowGL (cosetRow F q) (rowPivot (cosetRow F q)) (rowPivot_spec (cosetRow_ne_zero F q))

omit [NumberField F] in
theorem lastRowStandard_out_mul_cosetGamma_inv (q : UnipotentRationalCosets F (j + 1)) :
    LastRowStandard F (q.out * (cosetGamma F q)⁻¹) :=
  lastRow_mul_inv_eq (fun b => by rw [cosetGamma, rowGL_last]; rfl)

/-- A matrix `g'` with `q.out γ_ξ⁻¹ ∈ N_(j+1)(F) diag(g', 1)`. -/
def cosetRestRep (q : UnipotentRationalCosets F (j + 1)) : RationalGL F j :=
  (exists_unitriangular_mul_padGL _ (lastRowStandard_out_mul_cosetGamma_inv F q)).choose

omit [NumberField F] in
theorem cosetRestRep_spec (q : UnipotentRationalCosets F (j + 1)) :
    ∃ n : Matrix (Fin (j + 1)) (Fin (j + 1)) F, IsUnitriangular n ∧
      n * (padGL (Nat.le_succ j) (cosetRestRep F q) : Matrix (Fin (j + 1)) (Fin (j + 1)) F) =
        ((q.out * (cosetGamma F q)⁻¹ : RationalGL F (j + 1)) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) F) :=
  (exists_unitriangular_mul_padGL _ (lastRowStandard_out_mul_cosetGamma_inv F q)).choose_spec

/-- The coset `N_j(F) g'` of the remaining block. -/
def cosetRest (q : UnipotentRationalCosets F (j + 1)) : UnipotentRationalCosets F j :=
  Quotient.mk _ (cosetRestRep F q)

theorem padGL_mem_rationalUpperUnipotent {u : RationalGL F j}
    (hu : u ∈ rationalUpperUnipotent F j) :
    padGL (Nat.le_succ j) u ∈ rationalUpperUnipotent F (j + 1) := by
  rw [mem_rationalUpperUnipotent_iff] at hu ⊢
  exact isUnitriangular_padGL _ _ hu

/-- **Decomposition.** `q.out ∈ N_(j+1)(F) diag((cosetRest q).out, 1) γ_ξ`. -/
theorem rightRel_cosetRest (q : UnipotentRationalCosets F (j + 1)) :
    QuotientGroup.rightRel (rationalUpperUnipotent F (j + 1))
      (padGL (Nat.le_succ j) (cosetRest F q).out * cosetGamma F q) q.out := by
  rw [QuotientGroup.rightRel_apply]
  obtain ⟨n, hn, hprod⟩ := cosetRestRep_spec F q
  have hr : QuotientGroup.rightRel (rationalUpperUnipotent F j) (cosetRest F q).out
      (cosetRestRep F q) := Quotient.exact (Quotient.out_eq _)
  have hu := QuotientGroup.rightRel_apply.mp hr
  set u := cosetRestRep F q * (cosetRest F q).out⁻¹ with hudef
  have hpu := padGL_mem_rationalUpperUnipotent F hu
  have hnmem : unitriangularUnit n hn ∈ rationalUpperUnipotent F (j + 1) :=
    (mem_rationalUpperUnipotent_iff F _).mpr hn
  have key : q.out * (padGL (Nat.le_succ j) (cosetRest F q).out * cosetGamma F q)⁻¹ =
      unitriangularUnit n hn * padGL (Nat.le_succ j) u := by
    apply Units.ext
    have h1 : q.out = unitriangularUnit n hn * padGL (Nat.le_succ j) (cosetRestRep F q) *
        cosetGamma F q := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      change q.out.val = n * _ * _
      rw [hprod, ← Units.val_mul, inv_mul_cancel_right]
    rw [h1, hudef, map_mul, map_inv]
    simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  rw [key]
  exact Subgroup.mul_mem _ hnmem hpu

/-- **Injectivity.** A coset is determined by its last row and its remaining block. -/
theorem cosetRow_cosetRest_injective :
    Function.Injective fun q : UnipotentRationalCosets F (j + 1) =>
      (cosetRow F q, cosetRest F q) := by
  intro q₁ q₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hγ : cosetGamma F q₁ = cosetGamma F q₂ := by
    apply Units.ext
    simp only [cosetGamma, coe_rowGL]
    rw [h1]
  rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
  apply Quotient.sound
  have e1 := rightRel_cosetRest F q₁
  have e2 := rightRel_cosetRest F q₂
  rw [h2, hγ] at e1
  exact (QuotientGroup.rightRel (rationalUpperUnipotent F (j + 1))).iseqv.trans
    ((QuotientGroup.rightRel (rationalUpperUnipotent F (j + 1))).iseqv.symm e1) e2

end Cosets

section Whittaker

variable (F : Type u) [Field F] [NumberField F] {r j : ℕ} (hj : j < r)
  (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
  (f : Points F (r + 1) → ℂ)
  (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)

include hψ hfΓ

/-- `W_f(diag(q, I) y) = W_f(diag(q', I) diag(γ_ξ, I) y)`. -/
theorem whittaker_padRational_coset (q : UnipotentRationalCosets F (j + 1))
    (y : Points F (r + 1)) :
    whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) q.out * y) =
      whittaker F r ψ f (padRational F (by omega : j ≤ r + 1) (cosetRest F q).out *
        (padRational F (by omega : j + 1 ≤ r + 1) (cosetGamma F q) * y)) := by
  rw [whittaker_padRational_of_rightRel F ψ hψ f hfΓ _ (rightRel_cosetRest F q), padRational_mul,
    padRational_padGL, mul_assoc]

end Whittaker

section Heights

variable {F : Type u} [Field F] [NumberField F] {k : ℕ}

open scoped Classical

theorem norm_mixedEmbedding_natCast_mul_le (M : ℕ) (x : F) :
    ‖mixedEmbedding F ((M : F) * x)‖ ≤ M * ‖mixedEmbedding F x‖ := by
  have h := norm_mixedEmbedding_mul_le F (M : F) x
  rwa [norm_mixedEmbedding_natCast] at h

/-- **Height of `γ_ξ`.** If `M ξ = v` with `M` a positive integer, `v` integral of size at most
`N ≥ 1`, and `ξ_i ≠ 0`, then `rowGL ξ i` has height at most `(M N^d, e)` for some positive
integer `e ≤ M N^d`. -/
theorem exists_heightLE_rowGL {M : ℕ} (hM : 0 < M) {ξ : Fin (k + 1) → F}
    (v : Fin (k + 1) → 𝓞 F) (hv : ∀ b, (M : F) * ξ b = (v b : F)) {N : ℝ} (hN1 : 1 ≤ N)
    (hN : ∀ b, ‖mixedEmbedding F (v b : F)‖ ≤ N) {i : Fin (k + 1)} (hi : ξ i ≠ 0) :
    ∃ e : ℕ, 0 < e ∧ (e : ℝ) ≤ M * N ^ Module.finrank ℚ F ∧
      HeightLE F (M * N ^ Module.finrank ℚ F) e (rowGL ξ i hi) := by
  set d := Module.finrank ℚ F with hd
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hvi : v i ≠ 0 := by
    intro h
    have := hv i
    rw [h] at this
    have h0 : (M : F) * ξ i = 0 := this.trans (by simp)
    exact hi ((mul_eq_zero.mp h0).resolve_left hMF)
  have hvi' : (v i : F) ≠ 0 := (Subalgebra.coe_eq_zero _).not.mpr hvi
  obtain ⟨E, hE0, hEle, hEint⟩ := exists_nat_inv_integral F hvi (hN i)
  have hinv := norm_mixedEmbedding_inv_le F hvi (hN i)
  have hN0 : 0 ≤ N := zero_le_one.trans hN1
  have hNd : N ≤ N ^ d := le_self_pow₀ hN1 (by omega)
  have hNd' : N * N ^ (d - 1) = N ^ d := by
    rw [← pow_succ']
    congr 1
    omega
  have hT1 : (1 : ℝ) ≤ M * N ^ d := one_le_mul_of_one_le_of_one_le hM1 (one_le_pow₀ hN1)
  have hξ : ∀ b, ξ b = (v b : F) / M := fun b => by
    rw [← hv b]
    field_simp
  refine ⟨M * E, Nat.mul_pos hM hE0, ?_, ?_, ?_⟩
  · push_cast
    calc (M : ℝ) * E ≤ M * N ^ d := mul_le_mul_of_nonneg_left hEle (Nat.cast_nonneg _)
      _ ≤ M * N ^ d := le_rfl
  · -- entries of `rowMatrix`
    intro a b
    rw [coe_rowGL]
    simp only [rowMatrix, Matrix.of_apply]
    split_ifs
    · refine ⟨?_, ?_⟩
      · rw [hξ, norm_mixedEmbedding_div_natCast]
        calc ‖mixedEmbedding F (v b : F)‖ / M ≤ ‖mixedEmbedding F (v b : F)‖ :=
              div_le_self (norm_nonneg _) hM1
          _ ≤ N := hN b
          _ ≤ N ^ d := hNd
          _ ≤ M * N ^ d := le_mul_of_one_le_left (pow_nonneg hN0 _) hM1
      · have h : ((M * E : ℕ) : F) * ξ b = (E : F) * (v b : F) := by
          rw [← hv b]
          push_cast
          ring
        rw [h]
        exact (isIntegral_natCast E).mul (v b).isIntegral_coe
    · refine ⟨(norm_mixedEmbedding_one_le F).trans hT1, ?_⟩
      rw [mul_one]
      exact isIntegral_natCast _
    · refine ⟨?_, ?_⟩
      · rw [map_zero, norm_zero]
        exact zero_le_one.trans hT1
      · rw [mul_zero]
        exact isIntegral_zero
  · -- entries of `rowMatrixInv`
    intro a b
    rw [coe_rowGL_inv]
    simp only [rowMatrixInv, Matrix.of_apply]
    have hξi : (ξ i)⁻¹ = (M : F) * (v i : F)⁻¹ := by
      rw [hξ i]
      field_simp
    have hquot : ∀ c, ξ c * (ξ i)⁻¹ = (v c : F) * (v i : F)⁻¹ := fun c => by
      rw [hξ c, hξ i]
      field_simp
    split_ifs
    · refine ⟨?_, ?_⟩
      · rw [hξi]
        calc ‖mixedEmbedding F ((M : F) * (v i : F)⁻¹)‖
            ≤ M * ‖mixedEmbedding F (v i : F)⁻¹‖ := norm_mixedEmbedding_natCast_mul_le M _
          _ ≤ M * N ^ (d - 1) := mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
          _ ≤ M * N ^ d := mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hN1 (Nat.sub_le d 1)) (Nat.cast_nonneg _)
      · have h : ((M * E : ℕ) : F) * (ξ i)⁻¹ = ((M * M : ℕ) : F) * ((E : F) * (v i : F)⁻¹) := by
          rw [hξi]
          push_cast
          ring
        rw [h]
        exact (isIntegral_natCast _).mul hEint
    · refine ⟨?_, ?_⟩
      · rw [map_neg, norm_neg, hquot]
        calc ‖mixedEmbedding F ((v _ : F) * (v i : F)⁻¹)‖
            ≤ ‖mixedEmbedding F (v _ : F)‖ * ‖mixedEmbedding F (v i : F)⁻¹‖ :=
              norm_mixedEmbedding_mul_le F _ _
          _ ≤ N * N ^ (d - 1) := mul_le_mul (hN _) hinv (norm_nonneg _) hN0
          _ = N ^ d := hNd'
          _ ≤ M * N ^ d := le_mul_of_one_le_left (pow_nonneg hN0 _) hM1
      · rw [hquot]
        have h : ((M * E : ℕ) : F) * -((v (Equiv.swap i (Fin.last k) b) : F) * (v i : F)⁻¹) =
            -((M : F) * (v (Equiv.swap i (Fin.last k) b) : F) * ((E : F) * (v i : F)⁻¹)) := by
          push_cast
          ring
        rw [h]
        exact (((isIntegral_natCast M).mul (v _).isIntegral_coe).mul hEint).neg
    · refine ⟨(norm_mixedEmbedding_one_le F).trans hT1, ?_⟩
      rw [mul_one]
      exact isIntegral_natCast _
    · refine ⟨?_, ?_⟩
      · rw [map_zero, norm_zero]
        exact zero_le_one.trans hT1
      · rw [mul_zero]
        exact isIntegral_zero

end Heights

end Langlands.Global.RankinSelbergGlobal.Unfolding
