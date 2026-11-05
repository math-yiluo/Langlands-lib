import Langlands.GroupScheme.SplitExistence.RootExp

/-! # Root operators with integral Lie brackets

The input of the derivation of the Chevalley commutator relations: divided-power root operators
`e j i` on `ℤ^n` (as in `ChevalleyData`) whose first divided powers `E_j = e j 1` satisfy the
integral bracket relation `[E_j, E_j'] ∈ {0} ∪ ℤ • E_k` with `root k = root j + root j'`.

This file proves the expansion `x_j(g) B x_j(-g) = Σ_m g^m σ_m(B)` of conjugation by a root
exponential `x_j(g) = divExp (e j) g` over any commutative ring, where
`σ_m(B) = Σ_{i + i' = m} (-1)^{i'} e_j^{(i)} B e_j^{(i')}` satisfies
`(m + 1) σ_{m+1}(B) = [E_j, σ_m(B)]`. -/

noncomputable section

universe u

open Matrix Finset

namespace Langlands.GroupScheme.SplitExistence

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]

/-- Divided-power root operators on `ℤ^n` with weights `wt` and integral Lie brackets: the
fields of `ChevalleyData` concerning the root operators, together with the bracket relation
`[e j 1, e j' 1] = 0` or `= c • e k 1` with `root k = root j + root j'` whenever
`root j' ≠ -root j`. -/
structure LieRootData (P : RootDatum J X Y) where
  n : ℕ
  wt : Fin n → X
  e : J → ℕ → Matrix (Fin n) (Fin n) ℤ
  e_zero : ∀ j, e j 0 = 1
  e_mul : ∀ j a c, e j a * e j c = ((a + c).choose a : ℤ) • e j (a + c)
  e_eq_zero : ∀ j k, n < k → e j k = 0
  e_weight : ∀ j k c d, e j k c d ≠ 0 → wt c = wt d + k • P.root j
  e_one_map_ne_zero : ∀ j (p : ℕ), p.Prime → (e j 1).map (Int.castRingHom (ZMod p)) ≠ 0
  lie_e_e : ∀ j j', P.root j' ≠ -P.root j →
    e j 1 * e j' 1 - e j' 1 * e j 1 = 0 ∨
      ∃ (k : J) (c : ℤ), P.root k = P.root j + P.root j' ∧
        e j 1 * e j' 1 - e j' 1 * e j 1 = c • e k 1

namespace LieRootData

variable {P : RootDatum J X Y} (D : LieRootData P)

theorem isDividedPowerFamily (j : J) : IsDividedPowerFamily (D.e j) :=
  ⟨D.e_zero j, D.e_mul j, D.e_eq_zero j⟩

variable (R : Type*) [CommRing R]

/-- The divided power `e_j^{(i)}` as a matrix over `R`. -/
def em (j : J) (i : ℕ) : Matrix (Fin D.n) (Fin D.n) R :=
  (D.e j i).map (Int.castRingHom R)

/-- The root operator `E_j = e_j^{(1)}` as a matrix over `R`. -/
abbrev E (j : J) : Matrix (Fin D.n) (Fin D.n) R :=
  D.em R j 1

variable {R}

theorem em_zero (j : J) : D.em R j 0 = 1 := by
  simp [em, D.e_zero]

theorem em_eq_zero (j : J) {k : ℕ} (hk : D.n < k) : D.em R j k = 0 := by
  simp [em, D.e_eq_zero j k hk]

theorem em_mul_em (j : J) (a c : ℕ) :
    D.em R j a * D.em R j c = (((a + c).choose a : ℕ) : R) • D.em R j (a + c) := by
  rw [em, em, em, ← Matrix.map_mul, D.e_mul]
  ext x y
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul,
    Int.cast_natCast]

theorem E_mul_em (j : J) (i : ℕ) :
    D.E R j * D.em R j i = ((i + 1 : ℕ) : R) • D.em R j (i + 1) := by
  rw [E, em_mul_em, Nat.choose_one_right, add_comm 1 i]

theorem em_mul_E (j : J) (i : ℕ) :
    D.em R j i * D.E R j = ((i + 1 : ℕ) : R) • D.em R j (i + 1) := by
  rw [E, em_mul_em, Nat.choose_succ_self_right]

theorem divExp_eq (j : J) (f : R) :
    divExp (D.e j) f = ∑ i ∈ range (D.n + 1), f ^ i • D.em R j i :=
  rfl

theorem commute_E_em (j : J) (i : ℕ) : Commute (D.E R j) (D.em R j i) := by
  rw [Commute, SemiconjBy, E_mul_em, em_mul_E]

theorem commute_E_divExp (j : J) (f : R) : Commute (D.E R j) (divExp (D.e j) f) := by
  rw [divExp_eq]
  exact Commute.sum_right _ _ _ fun i _ => (D.commute_E_em j i).smul_right _

variable (R) in
/-- `σ_m(B) = Σ_{i + i' = m} (-1)^{i'} e_j^{(i)} B e_j^{(i')}`, the coefficient of `g^m` in
`x_j(g) B x_j(-g)`. -/
def sigma (j : J) (m : ℕ) (B : Matrix (Fin D.n) (Fin D.n) R) : Matrix (Fin D.n) (Fin D.n) R :=
  ∑ p ∈ antidiagonal m, ((-1 : R) ^ p.2) • (D.em R j p.1 * B * D.em R j p.2)

theorem sigma_zero (j : J) (B : Matrix (Fin D.n) (Fin D.n) R) : D.sigma R j 0 B = B := by
  simp [sigma, em_zero]

/-- The recursion `(m + 1) σ_{m+1}(B) = E_j σ_m(B) - σ_m(B) E_j`. -/
theorem sigma_succ (j : J) (m : ℕ) (B : Matrix (Fin D.n) (Fin D.n) R) :
    ((m + 1 : ℕ) : R) • D.sigma R j (m + 1) B =
      D.E R j * D.sigma R j m B - D.sigma R j m B * D.E R j := by
  set F : ℕ × ℕ → Matrix (Fin D.n) (Fin D.n) R :=
    fun p => ((-1 : R) ^ p.2) • (D.em R j p.1 * B * D.em R j p.2) with hF
  have hsplit : ((m + 1 : ℕ) : R) • D.sigma R j (m + 1) B =
      ∑ p ∈ antidiagonal (m + 1), ((p.1 : ℕ) : R) • F p +
        ∑ p ∈ antidiagonal (m + 1), ((p.2 : ℕ) : R) • F p := by
    rw [sigma, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [← add_smul, ← Nat.cast_add, hp]
  have h1 : ∑ p ∈ antidiagonal (m + 1), ((p.1 : ℕ) : R) • F p = D.E R j * D.sigma R j m B := by
    rw [Finset.Nat.sum_antidiagonal_succ, sigma, Finset.mul_sum]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hF, Matrix.mul_smul, ← Matrix.mul_assoc, E_mul_em, Matrix.smul_mul, smul_smul,
      mul_comm]
  have h2 : ∑ p ∈ antidiagonal (m + 1), ((p.2 : ℕ) : R) • F p = -(D.sigma R j m B * D.E R j) := by
    rw [Finset.Nat.sum_antidiagonal_succ', sigma, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hF, Matrix.smul_mul, Matrix.mul_assoc, em_mul_E, Matrix.mul_smul, smul_smul,
      pow_succ, ← neg_smul]
    congr 1
    ring
  rw [hsplit, h1, h2, sub_eq_add_neg]

/-- Conjugation by a root exponential: `x_j(g) B x_j(-g) = Σ_m g^m σ_m(B)`. -/
theorem conj_eq_sum (j : J) (g : R) (B : Matrix (Fin D.n) (Fin D.n) R) :
    divExp (D.e j) g * B * divExp (D.e j) (-g) =
      ∑ m ∈ range (2 * D.n + 1), g ^ m • D.sigma R j m B := by
  set F : ℕ × ℕ → Matrix (Fin D.n) (Fin D.n) R :=
    fun p => g ^ (p.1 + p.2) • (((-1 : R) ^ p.2) • (D.em R j p.1 * B * D.em R j p.2)) with hF
  have hL : divExp (D.e j) g * B * divExp (D.e j) (-g) =
      ∑ p ∈ range (D.n + 1) ×ˢ range (D.n + 1), F p := by
    rw [divExp_eq, divExp_eq, Finset.sum_mul, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [hF, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_pow g, pow_add]
    congr 1
    ring
  have hR : ∑ m ∈ range (2 * D.n + 1), g ^ m • D.sigma R j m B =
      ∑ m ∈ range (2 * D.n + 1), ∑ p ∈ antidiagonal m, F p := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sigma, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    simp only [hF, hp]
  have hFzero : ∀ p : ℕ × ℕ, (D.n < p.1 ∨ D.n < p.2) → F p = 0 := by
    rintro p (h | h)
    · simp [hF, D.em_eq_zero j h]
    · simp [hF, D.em_eq_zero j h]
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

end LieRootData

end Langlands.GroupScheme.SplitExistence
