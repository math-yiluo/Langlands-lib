import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Upper triangular times unitary factorization with entry bounds -/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace Langlands.LinearAlgebra.TriangularUnitary

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ## Upper Cholesky factorization -/

/-- The conjugate transpose of a lower triangular matrix is upper triangular. -/
theorem isUpperTriangular_conjTranspose {L : Matrix (Fin n) (Fin n) 𝕜}
    (hL : L.IsLowerTriangular) : Lᴴ.IsUpperTriangular := by
  intro i j hij
  have h0 : L j i = 0 := hL (by simpa [OrderDual.toDual_lt_toDual] using hij)
  rw [conjTranspose_apply, h0, star_zero]

/-- An upper triangular matrix times a diagonal matrix is upper triangular. -/
theorem isUpperTriangular_mul_diagonal {b : Matrix (Fin n) (Fin n) 𝕜}
    (hb : b.IsUpperTriangular) (s : Fin n → 𝕜) : (b * diagonal s).IsUpperTriangular := by
  intro i j hij
  rw [Matrix.mul_diagonal, hb hij, zero_mul]

/-- Every positive definite matrix is `b * bᴴ` for an invertible upper triangular `b`.
The factor is `Lᴴ D^{-1/2}`, where `L P⁻¹ Lᴴ = D` is Mathlib's LDL decomposition of
`P⁻¹`. -/
theorem exists_upperTriangular_mul_conjTranspose {P : Matrix (Fin n) (Fin n) 𝕜}
    (hP : P.PosDef) :
    ∃ b : Matrix (Fin n) (Fin n) 𝕜, b.IsUpperTriangular ∧ IsUnit b ∧ b * bᴴ = P := by
  classical
  have hQ : P⁻¹.PosDef := hP.inv
  set L := LDL.lowerInv hQ with hLdef
  have hLunit : IsUnit L := isUnit_of_invertible L
  have hLdet : IsUnit L.det := (isUnit_iff_isUnit_det L).mp hLunit
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  set D := L * P⁻¹ * Lᴴ with hDdef
  have hD : D.PosDef :=
    hQ.mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.mpr hLunit)
  have hDdiag : D = diagonal (LDL.diagEntries hQ) := (LDL.diag_eq_lowerInv_conj hQ).symm
  have hpos : ∀ i, ∃ x : ℝ, 0 < x ∧ (x : 𝕜) = LDL.diagEntries hQ i := by
    intro i
    have h := hD.diag_pos (i := i)
    rw [hDdiag, diagonal_apply_eq] at h
    exact RCLike.pos_iff_exists_ofReal.mp h
  choose d hd0 hd using hpos
  set s : Fin n → 𝕜 := fun i => (((Real.sqrt (d i))⁻¹ : ℝ) : 𝕜) with hsdef
  set E : Matrix (Fin n) (Fin n) 𝕜 := diagonal fun i => (((d i)⁻¹ : ℝ) : 𝕜) with hEdef
  have hss : diagonal s * (diagonal s)ᴴ = E := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, hEdef]
    congr 1
    funext i
    simp only [hsdef, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal]
    rw [← RCLike.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (hd0 i).le]
  have hED : E * D = 1 := by
    rw [hDdiag, hEdef, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← hd i, ← RCLike.ofReal_mul, inv_mul_cancel₀ (hd0 i).ne', RCLike.ofReal_one]
  have hLH : IsUnit Lᴴ.det := by
    rw [det_conjTranspose]
    exact hLdet.star
  refine ⟨Lᴴ * diagonal s, isUpperTriangular_mul_diagonal (isUpperTriangular_conjTranspose
    (LDL.isLowerTriangular_lowerInv hQ)) s, ?_, ?_⟩
  · refine (isUnit_iff_isUnit_det _).mpr ?_
    rw [det_mul]
    refine hLH.mul ?_
    rw [det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    simp only [hsdef, ne_eq, RCLike.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.mpr (hd0 i)).ne'
  · have hX : Lᴴ * E * L * P⁻¹ = 1 := by
      calc Lᴴ * E * L * P⁻¹ = Lᴴ * (E * D) * Lᴴ⁻¹ := by
            rw [hDdef]
            simp only [Matrix.mul_assoc]
            rw [mul_nonsing_inv _ hLH, Matrix.mul_one]
        _ = 1 := by rw [hED, Matrix.mul_one, mul_nonsing_inv _ hLH]
    have hX' : Lᴴ * E * L = P := by
      calc Lᴴ * E * L = Lᴴ * E * L * P⁻¹ * P := by
            rw [Matrix.mul_assoc (Lᴴ * E * L), nonsing_inv_mul _ hPdet, Matrix.mul_one]
        _ = P := by rw [hX, Matrix.one_mul]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, ← hX', ← hss]
    simp only [Matrix.mul_assoc]

/-! ## Upper triangular times unitary -/

/-- `g = b * u` with `b` an invertible upper triangular matrix and `u` a unitary matrix. -/
def IsTriangularUnitaryFactorization (g b u : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  b.IsUpperTriangular ∧ IsUnit b ∧ u ∈ unitaryGroup (Fin n) 𝕜 ∧ g = b * u

/-- Every invertible matrix over an `RCLike` field is an invertible upper triangular
matrix times a unitary matrix. -/
theorem exists_upperTriangular_mul_unitary (g : Matrix (Fin n) (Fin n) 𝕜) (hg : IsUnit g) :
    ∃ b u : Matrix (Fin n) (Fin n) 𝕜, IsTriangularUnitaryFactorization g b u := by
  have hP : (g * gᴴ).PosDef := PosDef.mul_conjTranspose_self g (vecMul_injective_iff_isUnit.mpr hg)
  obtain ⟨b, hb, hbu, hbb⟩ := exists_upperTriangular_mul_conjTranspose hP
  have hbdet : IsUnit b.det := (isUnit_iff_isUnit_det b).mp hbu
  have hbHdet : IsUnit bᴴ.det := by
    rw [det_conjTranspose]
    exact hbdet.star
  refine ⟨b, b⁻¹ * g, hb, hbu, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_nonsing_inv]
    calc b⁻¹ * g * (gᴴ * bᴴ⁻¹) = b⁻¹ * (g * gᴴ) * bᴴ⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← hbb, ← Matrix.mul_assoc, nonsing_inv_mul _ hbdet, Matrix.one_mul,
            mul_nonsing_inv _ hbHdet]
  · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hbdet, Matrix.one_mul]

/-! ## Entry bounds -/

/-- An entry of `M` is bounded by the real part of the corresponding diagonal entry of
`M * Mᴴ`, that is, by the Euclidean norm of its row. -/
theorem norm_sq_le_re_mul_conjTranspose_self (M : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) :
    ‖M i j‖ ^ 2 ≤ RCLike.re ((M * Mᴴ) i i) := by
  have h : RCLike.re ((M * Mᴴ) i i) = ∑ k, ‖M i k‖ ^ 2 := by
    rw [mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  rw [h]
  exact Finset.single_le_sum (f := fun k => ‖M i k‖ ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ j)

/-- Rows of a matrix with entries bounded by `B` have squared Euclidean norm at most
`n * B ^ 2`. -/
theorem re_mul_conjTranspose_self_le (M : Matrix (Fin n) (Fin n) 𝕜) {B : ℝ}
    (hB : ∀ i j, ‖M i j‖ ≤ B) (i : Fin n) :
    RCLike.re ((M * Mᴴ) i i) ≤ n * B ^ 2 := by
  have h : RCLike.re ((M * Mᴴ) i i) = ∑ k, ‖M i k‖ ^ 2 := by
    rw [mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  rw [h]
  calc ∑ k, ‖M i k‖ ^ 2 ≤ ∑ _k : Fin n, B ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hB i k) 2
    _ = n * B ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Entries of a unitary matrix have norm at most one. -/
theorem norm_le_one_of_mem_unitaryGroup {u : Matrix (Fin n) (Fin n) 𝕜}
    (hu : u ∈ unitaryGroup (Fin n) 𝕜) (i j : Fin n) : ‖u i j‖ ≤ 1 := by
  have h := norm_sq_le_re_mul_conjTranspose_self u i j
  rw [← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hu, one_apply_eq, RCLike.one_re] at h
  nlinarith [norm_nonneg (u i j)]

/-- Right multiplication by a unitary matrix preserves `M * Mᴴ`. -/
theorem mul_unitary_mul_conjTranspose {M u : Matrix (Fin n) (Fin n) 𝕜}
    (hu : u ∈ unitaryGroup (Fin n) 𝕜) : M * u * (M * u)ᴴ = M * Mᴴ := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc u, ← star_eq_conjTranspose u,
    mem_unitaryGroup_iff.mp hu, Matrix.one_mul]

/-- If the entries of `M` are bounded by `B ≥ 0`, so are those of `M * u` for unitary
`u`, up to the factor `√n`. -/
theorem norm_mul_unitary_le {M u : Matrix (Fin n) (Fin n) 𝕜}
    (hu : u ∈ unitaryGroup (Fin n) 𝕜) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, ‖M i j‖ ≤ B)
    (i j : Fin n) : ‖(M * u) i j‖ ≤ Real.sqrt n * B := by
  have h := norm_sq_le_re_mul_conjTranspose_self (M * u) i j
  rw [mul_unitary_mul_conjTranspose hu] at h
  have h' := h.trans (re_mul_conjTranspose_self_le M hB i)
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hB0, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt h'

/-- If the entries of `M` are bounded by `B ≥ 0`, so are those of `u * M` for unitary
`u`, up to the factor `√n`. -/
theorem norm_unitary_mul_le {M u : Matrix (Fin n) (Fin n) 𝕜}
    (hu : u ∈ unitaryGroup (Fin n) 𝕜) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, ‖M i j‖ ≤ B)
    (i j : Fin n) : ‖(u * M) i j‖ ≤ Real.sqrt n * B := by
  have hu' : uᴴ ∈ unitaryGroup (Fin n) 𝕜 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hu
  have hM' : ∀ i j, ‖Mᴴ i j‖ ≤ B := fun i j => by
    rw [conjTranspose_apply, norm_star]
    exact hB j i
  have h := norm_mul_unitary_le hu' hB0 hM' j i
  rwa [← conjTranspose_mul, conjTranspose_apply, norm_star] at h

/-! ## Triangular factors of bounded matrices -/

/-- The diagonal entries of an invertible upper triangular matrix and of its inverse are
mutually inverse. -/
theorem inv_apply_self_mul_apply_self {b : Matrix (Fin n) (Fin n) 𝕜}
    (hb : b.IsUpperTriangular) (hbu : IsUnit b) (i : Fin n) : b⁻¹ i i * b i i = 1 := by
  have hbdet : IsUnit b.det := (isUnit_iff_isUnit_det b).mp hbu
  let _ : Invertible b := invertibleOfIsUnitDet b hbdet
  have hinv : b⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular hb
  have h := congrFun (congrFun (nonsing_inv_mul b hbdet) i) i
  rw [mul_apply, one_apply_eq] at h
  rw [← h, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hinv hk, zero_mul]
    · rw [hb hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Bounded factors: if `g = b * u` with `b` invertible upper triangular and `u` unitary,
and the entries of `g` and `g⁻¹` are bounded by `B ≥ 0` and `B' ≥ 0`, then the entries of
`b` are bounded by `√n * B`, those of `b⁻¹` by `√n * B'`, and every diagonal entry of
`b` has norm at least `(√n * B')⁻¹`. -/
theorem bounds_of_isTriangularUnitaryFactorization {g b u : Matrix (Fin n) (Fin n) 𝕜}
    (hf : IsTriangularUnitaryFactorization g b u) {B B' : ℝ} (hB0 : 0 ≤ B) (hB'0 : 0 ≤ B')
    (hB : ∀ i j, ‖g i j‖ ≤ B) (hB' : ∀ i j, ‖g⁻¹ i j‖ ≤ B') :
    (∀ i j, ‖b i j‖ ≤ Real.sqrt n * B) ∧ (∀ i j, ‖b⁻¹ i j‖ ≤ Real.sqrt n * B') ∧
      ∀ i, (Real.sqrt n * B')⁻¹ ≤ ‖b i i‖ := by
  obtain ⟨hb, hbu, hu, hg⟩ := hf
  have hustar : u * star u = 1 := mem_unitaryGroup_iff.mp hu
  have hbg : b = g * star u := by
    rw [hg, Matrix.mul_assoc, hustar, Matrix.mul_one]
  have hbdet : IsUnit b.det := (isUnit_iff_isUnit_det b).mp hbu
  have hudet : IsUnit u.det := (isUnit_iff_isUnit_det u).mp (Unitary.isUnit_coe (U := ⟨u, hu⟩))
  have hbinv : b⁻¹ = u * g⁻¹ := by
    rw [hg, Matrix.mul_inv_rev, ← Matrix.mul_assoc, mul_nonsing_inv _ hudet, Matrix.one_mul]
  have hstar : star u ∈ unitaryGroup (Fin n) 𝕜 := Unitary.star_mem hu
  have h1 : ∀ i j, ‖b i j‖ ≤ Real.sqrt n * B := fun i j => by
    rw [hbg]
    exact norm_mul_unitary_le hstar hB0 hB i j
  have h2 : ∀ i j, ‖b⁻¹ i j‖ ≤ Real.sqrt n * B' := fun i j => by
    rw [hbinv]
    exact norm_unitary_mul_le hu hB'0 hB' i j
  refine ⟨h1, h2, fun i => ?_⟩
  have hprod := inv_apply_self_mul_apply_self hb hbu i
  have hnorm : ‖b⁻¹ i i‖ * ‖b i i‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  have hpos : 0 < ‖b⁻¹ i i‖ := by
    rcases (norm_nonneg (b⁻¹ i i)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hnorm
      exact absurd hnorm zero_ne_one
  calc (Real.sqrt n * B')⁻¹ ≤ ‖b⁻¹ i i‖⁻¹ := inv_anti₀ hpos (h2 i i)
    _ = ‖b i i‖ := (eq_inv_of_mul_eq_one_right hnorm).symm

end Langlands.LinearAlgebra.TriangularUnitary
