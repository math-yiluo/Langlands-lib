import Langlands.GroupScheme.SplitExistence.RootExp
import Langlands.GroupScheme.SplitExistence.RootLieAlgebra

/-!
# Conjugation by the exponential of a divided-power family

For a divided-power family `D` of integral `n × n` matrices (`IsDividedPowerFamily`), the
`k`-th power of `D 1` is `k! • D k` (`IsDividedPowerFamily.pow_one`), and conjugation by the
truncated exponential `divExp D g` over a commutative ring expands as
`divExp D g * B * divExp D (-g) = Σ_m g^m σ_m(B)` (`dpConj_eq_sum`), where
`σ_m(B) = Σ_{a + c = m} (-1)^c D_a B D_c` satisfies `(m + 1) σ_{m+1}(B) = [D 1, σ_m(B)]`
(`dpSigma_succ`). Consequently, over `ℚ`, conjugation by `divExp D s` preserves every subspace
that is stable under the commutator with `D 1` (`divExp_conj_mem`).

The expansion follows the proof of `LieRootData.conj_eq_sum` in the module
`Langlands.GroupScheme.SplitExistence.LieRootData`, for an arbitrary divided-power family.
-/

noncomputable section

open Matrix Finset

namespace Langlands.GroupScheme.SplitExistence

variable {n : ℕ} {D : ℕ → Matrix (Fin n) (Fin n) ℤ}

/-- `(D 1) ^ k = k! • D k` for a divided-power family. -/
theorem IsDividedPowerFamily.pow_one (hD : IsDividedPowerFamily D) (k : ℕ) :
    D 1 ^ k = (k.factorial : ℤ) • D k := by
  induction k with
  | zero => simp [hD.zero]
  | succ k ih =>
    rw [pow_succ', ih, Matrix.mul_smul, hD.mul 1 k, smul_smul, add_comm 1 k,
      Nat.choose_one_right, Nat.factorial_succ]
    congr 1
    push_cast
    ring

variable {R : Type*} [CommRing R]

/-- A scalar multiple of an integral matrix, mapped to `R`. -/
theorem map_intCast_zsmul (c : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) :
    (c • M).map (Int.castRingHom R) = (c : R) • M.map (Int.castRingHom R) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul]

theorem dp_one_mul (hD : IsDividedPowerFamily D) (i : ℕ) :
    (D 1).map (Int.castRingHom R) * (D i).map (Int.castRingHom R) =
      ((i + 1 : ℕ) : R) • (D (i + 1)).map (Int.castRingHom R) := by
  rw [← Matrix.map_mul, hD.mul 1 i, map_intCast_zsmul, add_comm 1 i, Nat.choose_one_right]
  push_cast
  rfl

theorem dp_mul_one (hD : IsDividedPowerFamily D) (i : ℕ) :
    (D i).map (Int.castRingHom R) * (D 1).map (Int.castRingHom R) =
      ((i + 1 : ℕ) : R) • (D (i + 1)).map (Int.castRingHom R) := by
  rw [← Matrix.map_mul, hD.mul i 1, map_intCast_zsmul, Nat.choose_succ_self_right]
  push_cast
  rfl

variable (D) in
/-- `σ_m(B) = Σ_{a + c = m} (-1)^c D_a B D_c`, the coefficient of `g^m` in
`divExp D g * B * divExp D (-g)`. -/
def dpSigma (m : ℕ) (B : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ∑ p ∈ antidiagonal m, ((-1 : R) ^ p.2) •
    ((D p.1).map (Int.castRingHom R) * B * (D p.2).map (Int.castRingHom R))

theorem dpSigma_zero (hD : IsDividedPowerFamily D) (B : Matrix (Fin n) (Fin n) R) :
    dpSigma D 0 B = B := by
  simp [dpSigma, hD.zero]

/-- The recursion `(m + 1) σ_{m+1}(B) = D_1 σ_m(B) - σ_m(B) D_1`. -/
theorem dpSigma_succ (hD : IsDividedPowerFamily D) (m : ℕ) (B : Matrix (Fin n) (Fin n) R) :
    ((m + 1 : ℕ) : R) • dpSigma D (m + 1) B =
      (D 1).map (Int.castRingHom R) * dpSigma D m B -
        dpSigma D m B * (D 1).map (Int.castRingHom R) := by
  set F : ℕ × ℕ → Matrix (Fin n) (Fin n) R := fun p => ((-1 : R) ^ p.2) •
    ((D p.1).map (Int.castRingHom R) * B * (D p.2).map (Int.castRingHom R)) with hF
  have hsplit : ((m + 1 : ℕ) : R) • dpSigma D (m + 1) B =
      ∑ p ∈ antidiagonal (m + 1), ((p.1 : ℕ) : R) • F p +
        ∑ p ∈ antidiagonal (m + 1), ((p.2 : ℕ) : R) • F p := by
    rw [dpSigma, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [← add_smul, ← Nat.cast_add, hp]
  have h1 : ∑ p ∈ antidiagonal (m + 1), ((p.1 : ℕ) : R) • F p =
      (D 1).map (Int.castRingHom R) * dpSigma D m B := by
    rw [Finset.Nat.sum_antidiagonal_succ, dpSigma, Finset.mul_sum]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hF, Matrix.mul_smul, ← Matrix.mul_assoc, dp_one_mul hD, Matrix.smul_mul,
      smul_smul, mul_comm]
  have h2 : ∑ p ∈ antidiagonal (m + 1), ((p.2 : ℕ) : R) • F p =
      -(dpSigma D m B * (D 1).map (Int.castRingHom R)) := by
    rw [Finset.Nat.sum_antidiagonal_succ', dpSigma, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hF, Matrix.smul_mul, Matrix.mul_assoc, dp_mul_one hD, Matrix.mul_smul, smul_smul,
      pow_succ, ← neg_smul]
    congr 1
    ring
  rw [hsplit, h1, h2, sub_eq_add_neg]

/-- Conjugation by a truncated exponential: `divExp D g * B * divExp D (-g) = Σ_m g^m σ_m(B)`. -/
theorem dpConj_eq_sum (hD : IsDividedPowerFamily D) (g : R) (B : Matrix (Fin n) (Fin n) R) :
    divExp D g * B * divExp D (-g) =
      ∑ m ∈ range (2 * n + 1), g ^ m • dpSigma D m B := by
  set F : ℕ × ℕ → Matrix (Fin n) (Fin n) R := fun p => g ^ (p.1 + p.2) • (((-1 : R) ^ p.2) •
    ((D p.1).map (Int.castRingHom R) * B * (D p.2).map (Int.castRingHom R))) with hF
  have hL : divExp D g * B * divExp D (-g) = ∑ p ∈ range (n + 1) ×ˢ range (n + 1), F p := by
    rw [divExp, divExp, Finset.sum_mul, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [hF, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_pow g, pow_add]
    congr 1
    ring
  have hR : ∑ m ∈ range (2 * n + 1), g ^ m • dpSigma D m B =
      ∑ m ∈ range (2 * n + 1), ∑ p ∈ antidiagonal m, F p := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [dpSigma, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    simp only [hF, hp]
  have hFzero : ∀ p : ℕ × ℕ, (n < p.1 ∨ n < p.2) → F p = 0 := by
    rintro p (h | h)
    · simp [hF, hD.eq_zero _ h]
    · simp [hF, hD.eq_zero _ h]
  rw [hL, hR, Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.2) ?_ ?_ ?_ ?_
  · rintro ⟨m, a, c⟩ hx hne
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    by_contra h
    exact hne (hFzero _ (by simp only at *; omega))
  · rintro ⟨m, a, c⟩ hx _ ⟨m', a', c'⟩ hx' _ h
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : m = m' := by omega
    subst this
    rfl
  · rintro ⟨a, c⟩ hp hf
    refine ⟨⟨a + c, a, c⟩, ?_, ?_, rfl⟩
    · simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal, and_true]
      omega
    · simpa using hf
  · rintro ⟨m, a, c⟩ _ _
    rfl

/-- Over `ℚ`, conjugation by the truncated exponential `divExp D s` preserves every subspace
that is stable under the commutator with `D 1`. -/
theorem divExp_conj_mem (hD : IsDividedPowerFamily D) {V : Submodule ℚ (Matrix (Fin n) (Fin n) ℚ)}
    (hV : ∀ y ∈ V, matAd ((D 1).map (Int.castRingHom ℚ)) y ∈ V) (s : ℚ)
    {x : Matrix (Fin n) (Fin n) ℚ} (hx : x ∈ V) :
    divExp D s * x * divExp D (-s) ∈ V := by
  have key : ∀ m, dpSigma D m x ∈ V := by
    intro m
    induction m with
    | zero => rwa [dpSigma_zero hD]
    | succ m ih =>
      have h := dpSigma_succ hD m x
      have hm : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have h2 : dpSigma D (m + 1) x = ((m + 1 : ℕ) : ℚ)⁻¹ •
          ((D 1).map (Int.castRingHom ℚ) * dpSigma D m x -
            dpSigma D m x * (D 1).map (Int.castRingHom ℚ)) := by
        rw [← h, smul_smul, inv_mul_cancel₀ hm, one_smul]
      rw [h2, ← matAd_apply]
      exact Submodule.smul_mem _ _ (hV _ ih)
  rw [dpConj_eq_sum hD]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (key m)

end Langlands.GroupScheme.SplitExistence
