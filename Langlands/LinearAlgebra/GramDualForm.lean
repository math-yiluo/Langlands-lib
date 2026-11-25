import Langlands.MathlibBase

/-! # The form dual to a weighted Gram matrix of a pairing

Given a pairing `P : X × Y → ℤ`, a basis `y_j` of `Y` and finitely supported multiplicities
`m : X → ℕ`, this module studies the rational Gram matrix
`M = ∑_ν m(ν) c(ν) c(ν)ᵀ` with `c(ν)_j = ⟨ν, y_j⟩`, and the form
`F(χ, χ') = c(χ)ᵀ M⁻¹ c(χ')` on `X`. -/

noncomputable section

open Function Matrix Module

namespace Langlands.LinearAlgebra.GramDual

variable {X Y ι : Type*} [AddCommGroup X] [AddCommGroup Y] [Fintype ι] [DecidableEq ι]
  (P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ) (yb : Basis ι ℤ Y) (m : X → ℕ)

/-- The coordinates `⟨χ, y_j⟩` of a character against the basis `y_j`. -/
def coord : X →ₗ[ℤ] ι → ℚ where
  toFun χ j := (P χ (yb j) : ℚ)
  map_add' χ χ' := by
    ext j
    simp
  map_smul' n χ := by
    ext j
    simp

omit [Fintype ι] [DecidableEq ι] in
theorem coord_apply (χ : X) (j : ι) : coord P yb χ j = (P χ (yb j) : ℚ) :=
  rfl

/-- The Gram matrix `∑_ν m(ν) c(ν) c(ν)ᵀ`. -/
def gram : Matrix ι ι ℚ :=
  ∑ᶠ ν, (m ν : ℚ) • vecMulVec (coord P yb ν) (coord P yb ν)

variable {m}

omit [AddCommGroup X] in
theorem support_subset_of_eq_zero {A : Type*} [Zero A] (hm : (support m).Finite) {f : X → A}
    (hf : ∀ ν, m ν = 0 → f ν = 0) : support f ⊆ ↑hm.toFinset := by
  intro ν hν
  rw [Set.Finite.coe_toFinset]
  exact fun h => hν (hf ν h)

omit [Fintype ι] [DecidableEq ι] in
theorem gram_eq_sum (hm : (support m).Finite) :
    gram P yb m = ∑ ν ∈ hm.toFinset, (m ν : ℚ) • vecMulVec (coord P yb ν) (coord P yb ν) :=
  finsum_eq_sum_of_support_subset _ (support_subset_of_eq_zero hm fun ν h => by simp [h])

omit [Fintype ι] [DecidableEq ι] in
theorem gram_apply (hm : (support m).Finite) (j l : ι) :
    gram P yb m j l = ∑ᶠ ν, (m ν : ℚ) * (coord P yb ν j * coord P yb ν l) := by
  rw [gram_eq_sum P yb hm, finsum_eq_sum_of_support_subset _
    (support_subset_of_eq_zero hm fun ν h => by simp [h]), Matrix.sum_apply]
  simp [vecMulVec_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem gram_transpose (hm : (support m).Finite) : (gram P yb m)ᵀ = gram P yb m := by
  rw [gram_eq_sum P yb hm, transpose_sum]
  simp [transpose_smul, transpose_vecMulVec]

omit [DecidableEq ι] in
theorem dotProduct_gram_mulVec (hm : (support m).Finite) (z : ι → ℚ) :
    z ⬝ᵥ (gram P yb m *ᵥ z) = ∑ ν ∈ hm.toFinset, (m ν : ℚ) * (coord P yb ν ⬝ᵥ z) ^ 2 := by
  rw [gram_eq_sum P yb hm, sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, dotProduct_comm z]
  ring

variable (hm : (support m).Finite) (hY : ∀ y : Y, y ≠ 0 → ∃ ν, m ν ≠ 0 ∧ P ν y ≠ 0)
include hm hY

omit [DecidableEq ι] in
/-- The Gram matrix is positive definite: `zᵀ M z = 0` forces `z = 0`. -/
theorem eq_zero_of_dotProduct_gram_mulVec_eq_zero {z : ι → ℚ}
    (hz : z ⬝ᵥ (gram P yb m *ᵥ z) = 0) : z = 0 := by
  rw [dotProduct_gram_mulVec P yb hm] at hz
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ => by positivity)).mp hz
  have horth : ∀ ν, m ν ≠ 0 → coord P yb ν ⬝ᵥ z = 0 := by
    intro ν hν
    have hmem : ν ∈ hm.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hν
    have h := hterm ν hmem
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (Nat.cast_eq_zero.mp h) hν
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) z
  choose zi hzi using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  let y : Y := ∑ j, zi j • yb j
  have hPy : ∀ ν, m ν ≠ 0 → P ν y = 0 := by
    intro ν hν
    have hcast : (P ν y : ℚ) = (b : ℤ) * (coord P yb ν ⬝ᵥ z) := by
      simp only [y, map_sum, map_zsmul, smul_eq_mul, Int.cast_sum, Int.cast_mul]
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := hzi j
      rw [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at h
      rw [h, coord_apply]
      ring
    rw [horth ν hν, mul_zero] at hcast
    exact_mod_cast hcast
  have hy0 : y = 0 := by
    by_contra hy
    obtain ⟨ν, hν, hne⟩ := hY y hy
    exact hne (hPy ν hν)
  have hzi0 : ∀ j, zi j = 0 := Fintype.linearIndependent_iff.mp yb.linearIndependent zi hy0
  ext j
  have h := hzi j
  rw [hzi0 j, algebraMap_int_eq, eq_intCast, Int.cast_zero, zsmul_eq_mul] at h
  rcases mul_eq_zero.mp h.symm with h | h
  · exact absurd (Int.cast_eq_zero.mp h) hb0
  · exact h

theorem det_gram_ne_zero : (gram P yb m).det ≠ 0 := by
  intro h
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  exact hz0 (eq_zero_of_dotProduct_gram_mulVec_eq_zero P yb hm hY
    (by rw [hz, dotProduct_zero]))

theorem isUnit_det_gram : IsUnit (gram P yb m).det :=
  isUnit_iff_ne_zero.mpr (det_gram_ne_zero P yb hm hY)

omit hm hY

variable (m) in
/-- The form `F(χ, χ') = c(χ)ᵀ M⁻¹ c(χ')`. -/
def form : X →ₗ[ℤ] X →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun χ χ' => coord P yb χ ⬝ᵥ ((gram P yb m)⁻¹ *ᵥ coord P yb χ'))
    (fun χ₁ χ₂ χ' => by rw [map_add, add_dotProduct])
    (fun n χ χ' => by rw [map_zsmul, smul_dotProduct])
    (fun χ χ₁ χ₂ => by rw [map_add, mulVec_add, dotProduct_add])
    (fun n χ χ' => by rw [map_zsmul, mulVec_smul, dotProduct_smul])

theorem form_apply (χ χ' : X) :
    form P yb m χ χ' = coord P yb χ ⬝ᵥ ((gram P yb m)⁻¹ *ᵥ coord P yb χ') :=
  rfl

include hm in
theorem form_comm (χ χ' : X) : form P yb m χ χ' = form P yb m χ' χ := by
  have hsymm : ((gram P yb m)⁻¹)ᵀ = (gram P yb m)⁻¹ := by
    rw [transpose_nonsing_inv, gram_transpose P yb hm]
  rw [form_apply, form_apply, dotProduct_mulVec, ← mulVec_transpose, hsymm, dotProduct_comm]

include hm hY in
theorem form_pos (hX : ∀ χ : X, χ ≠ 0 → ∃ y, P χ y ≠ 0) {χ : X} (hχ : χ ≠ 0) :
    0 < form P yb m χ χ := by
  set z := (gram P yb m)⁻¹ *ᵥ coord P yb χ with hz
  have hMz : gram P yb m *ᵥ z = coord P yb χ := by
    rw [hz, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_gram P yb hm hY), one_mulVec]
  have hF : form P yb m χ χ = z ⬝ᵥ (gram P yb m *ᵥ z) := by
    rw [form_apply, ← hz, hMz, dotProduct_comm]
  have hnn : 0 ≤ form P yb m χ χ := by
    rw [hF, dotProduct_gram_mulVec P yb hm]
    exact Finset.sum_nonneg fun ν _ => by positivity
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have hz0 : z = 0 := eq_zero_of_dotProduct_gram_mulVec_eq_zero P yb hm hY (by rw [← hF, h0])
  rw [hz0, mulVec_zero] at hMz
  obtain ⟨y, hy⟩ := hX χ hχ
  apply hy
  have hPχ : P χ = 0 := by
    refine yb.ext fun j => ?_
    have h := congrFun hMz j
    rw [Pi.zero_apply, coord_apply] at h
    rw [LinearMap.zero_apply]
    exact_mod_cast h.symm
  rw [hPχ, LinearMap.zero_apply]

include hm hY in
/-- The form is invariant under a bijection `s` of `X` preserving the multiplicities and
adjoint, for the pairing, to an endomorphism `s'` of `Y`. -/
theorem form_apply_apply_eq (s : X ≃ X) (s' : Y →ₗ[ℤ] Y)
    (hs : ∀ χ y, P (s χ) y = P χ (s' y)) (hms : ∀ ν, m (s ν) = m ν) (χ χ' : X) :
    form P yb m (s χ) (s χ') = form P yb m χ χ' := by
  let A : Matrix ι ι ℚ := Matrix.of fun j l => ((yb.repr (s' (yb j)) l : ℤ) : ℚ)
  have hc : ∀ χ, coord P yb (s χ) = A *ᵥ coord P yb χ := by
    intro χ
    ext j
    rw [coord_apply, hs, ← yb.sum_repr (s' (yb j)), map_sum]
    simp only [map_zsmul, smul_eq_mul, Int.cast_sum, Int.cast_mul, mulVec, dotProduct, A,
      Matrix.of_apply, coord_apply]
  have hgram : gram P yb m = A * gram P yb m * Aᵀ := by
    have hterm : ∀ ν, (m (s ν) : ℚ) • vecMulVec (coord P yb (s ν)) (coord P yb (s ν)) =
        A * ((m ν : ℚ) • vecMulVec (coord P yb ν) (coord P yb ν)) * Aᵀ := by
      intro ν
      rw [hms, hc, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul,
        vecMul_transpose]
    calc gram P yb m
        = ∑ᶠ ν, (m (s ν) : ℚ) • vecMulVec (coord P yb (s ν)) (coord P yb (s ν)) :=
          (finsum_comp_equiv s (f := fun ν =>
            (m ν : ℚ) • vecMulVec (coord P yb ν) (coord P yb ν))).symm
      _ = ∑ᶠ ν, A * ((m ν : ℚ) • vecMulVec (coord P yb ν) (coord P yb ν)) * Aᵀ :=
          finsum_congr hterm
      _ = A * gram P yb m * Aᵀ := by
          rw [finsum_eq_sum_of_support_subset _ (support_subset_of_eq_zero hm fun ν h => by
            simp [h]), gram_eq_sum P yb hm, Matrix.mul_sum, Matrix.sum_mul]
  have hdetA : IsUnit A.det := by
    refine isUnit_iff_ne_zero.mpr fun h => det_gram_ne_zero P yb hm hY ?_
    rw [hgram, det_mul, det_mul, h, zero_mul, zero_mul]
  have hdetAT : IsUnit Aᵀ.det := by rwa [det_transpose]
  have hinv : (gram P yb m)⁻¹ = Aᵀ⁻¹ * (gram P yb m)⁻¹ * A⁻¹ := by
    conv_lhs => rw [hgram]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have hkey : Aᵀ * (gram P yb m)⁻¹ * A = (gram P yb m)⁻¹ := by
    calc Aᵀ * (gram P yb m)⁻¹ * A = Aᵀ * (Aᵀ⁻¹ * (gram P yb m)⁻¹ * A⁻¹) * A := by
          rw [← hinv]
      _ = (Aᵀ * Aᵀ⁻¹) * (gram P yb m)⁻¹ * (A⁻¹ * A) := by
          simp only [Matrix.mul_assoc]
      _ = (gram P yb m)⁻¹ := by
          rw [mul_nonsing_inv _ hdetAT, nonsing_inv_mul _ hdetA, Matrix.one_mul,
            Matrix.mul_one]
  rw [form_apply, form_apply, hc, hc, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
    dotProduct_comm, mulVec_mulVec, mulVec_mulVec, hkey]

end Langlands.LinearAlgebra.GramDual
