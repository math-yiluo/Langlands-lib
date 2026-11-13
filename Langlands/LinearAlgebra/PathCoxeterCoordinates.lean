import Langlands.LinearAlgebra.PathCoxeterCharpoly

/-! # Coordinates of path Coxeter products with a pattern block -/

noncomputable section

open Polynomial Matrix

namespace Langlands.LinearAlgebra.PathCoxeter

variable {R : Type*} [CommRing R]

/-! ### The characteristic polynomial of an ordinary path product -/

/-- The characteristic polynomial of the ordinary path product on `2 k + 3` lines with
coordinates `γ`: `X^(2k+3) + Σ_{j<2k+2} (-1)^j γ_j X^(2k+2-j) - 1`. -/
def ordPoly (k : ℕ) (γ : ℕ → R) : R[X] :=
  X ^ (2 * k + 3) + (∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * C (γ j) * X ^ (2 * k + 2 - j))
    - 1

theorem charpoly_pprod_eq_ordPoly (k : ℕ) (c : ℕ → R) :
    (pprod (2 * k + 3) 0 (2 * k + 2) c).charpoly = ordPoly k c :=
  charpoly_pprod k c

theorem coeff_neg_one_pow_mul_C_mul_X_pow (j n m : ℕ) (r : R) :
    ((-1 : R[X]) ^ j * C r * X ^ n).coeff m = if m = n then (-1) ^ j * r else 0 := by
  rw [show ((-1 : R[X]) ^ j * C r) = C ((-1) ^ j * r) by simp, coeff_C_mul_X_pow]

theorem ordPoly_coeff (k : ℕ) (γ : ℕ → R) {j : ℕ} (hj : j < 2 * k + 2) :
    (ordPoly k γ).coeff (2 * k + 2 - j) = (-1) ^ j * γ j := by
  rw [ordPoly, coeff_sub, coeff_add, coeff_X_pow, ite_eq_right (by omega), coeff_one,
    ite_eq_right (by omega), finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [coeff_neg_one_pow_mul_C_mul_X_pow, ite_eq_left rfl]
    ring
  · intro i hi hij
    rw [Finset.mem_range] at hi
    rw [coeff_neg_one_pow_mul_C_mul_X_pow, ite_eq_right (by omega)]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

/-- The coordinates of an ordinary path product are determined by its characteristic
polynomial. -/
theorem eq_of_ordPoly_eq {k : ℕ} {γ γ' : ℕ → R} (h : ordPoly k γ = ordPoly k γ') {j : ℕ}
    (hj : j < 2 * k + 2) : γ j = γ' j := by
  have h1 := ordPoly_coeff k γ hj
  rw [h, ordPoly_coeff k γ' hj] at h1
  have h2 := congrArg (fun r => (-1) ^ j * r) h1
  simp only [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at h2
  exact h2.symm

/-! ### The shift identity -/

/-- The polynomial `-Σ_{j<2k+3} (-1)^j u_j X^(2k+2-j)`. -/
def qPoly (k : ℕ) (u : ℕ → R) : R[X] :=
  -∑ j ∈ Finset.range (2 * k + 3), (-1) ^ j * C (u j) * X ^ (2 * k + 2 - j)

/-- If `u 0 = u (2k+2) = -1`, then the ordinary path polynomial with coordinates
`u_j + u_(j+1) + δ [j = k + 1]` is `(X - 1) qPoly k u + (-1)^(k+1) δ X^(k+1)`. -/
theorem ordPoly_shift (k : ℕ) (u : ℕ → R) (h0 : u 0 = -1) (htop : u (2 * k + 2) = -1)
    (δ : R) :
    ordPoly k (fun j => u j + u (j + 1) + if j = k + 1 then δ else 0) =
      (X - 1) * qPoly k u + (-1) ^ (k + 1) * C δ * X ^ (k + 1) := by
  set S0 := ∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * C (u j) * X ^ (2 * k + 2 - j)
  set S1 := ∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * C (u (j + 1)) * X ^ (2 * k + 2 - j)
  have hsplit : (∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j *
      C (u j + u (j + 1) + if j = k + 1 then δ else 0) * X ^ (2 * k + 2 - j)) =
      S0 + S1 + (-1) ^ (k + 1) * C δ * X ^ (k + 1) := by
    have hδ : (∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j *
        C (if j = k + 1 then δ else 0) * X ^ (2 * k + 2 - j)) =
        (-1) ^ (k + 1) * C δ * X ^ (k + 1) := by
      rw [Finset.sum_eq_single (k + 1)]
      · rw [ite_eq_left rfl, show 2 * k + 2 - (k + 1) = k + 1 by omega]
      · intro j _ hj
        rw [ite_eq_right hj, map_zero, mul_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    rw [← hδ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, map_add]
    ring
  have hA : (∑ j ∈ Finset.range (2 * k + 3), (-1) ^ j * C (u j) * X ^ (2 * k + 2 - j)) =
      S0 - 1 := by
    rw [Finset.sum_range_succ, htop, Nat.sub_self, pow_zero, mul_one,
      (Even.neg_one_pow ⟨k + 1, by ring⟩ : (-1 : R[X]) ^ (2 * k + 2) = 1)]
    simp
    ring
  have hB : X * (∑ j ∈ Finset.range (2 * k + 3), (-1) ^ j * C (u j) * X ^ (2 * k + 2 - j)) =
      -X ^ (2 * k + 3) - S1 := by
    rw [Finset.sum_range_succ', h0, mul_add, Finset.mul_sum]
    have hs : ∀ j ∈ Finset.range (2 * k + 2),
        X * ((-1) ^ (j + 1) * C (u (j + 1)) * X ^ (2 * k + 2 - (j + 1))) =
          -((-1) ^ j * C (u (j + 1)) * X ^ (2 * k + 2 - j)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show 2 * k + 2 - j = (2 * k + 2 - (j + 1)) + 1 by omega]
      ring
    rw [Finset.sum_congr rfl hs, Finset.sum_neg_distrib]
    simp only [pow_zero, Nat.sub_zero, map_neg, map_one]
    ring
  rw [ordPoly, hsplit, qPoly, mul_neg, sub_mul, hB, one_mul, hA]
  ring

/-! ### Coordinates of a pattern product -/

/-- The auxiliary sequence of a pattern product: `-1` at `0`, the coordinates `d_0, …, d_(k-1)`
at `1, …, k`, the value `σ` at `k + 1`, the coordinates `d_(k+2), …, d_(2k+1)` at
`k + 2, …, 2k + 1`, and `-1` from `2k + 2` on. -/
def patU (k : ℕ) (d : ℕ → R) (σ : R) : ℕ → R := fun j =>
  if j = 0 then -1 else if j ≤ k then d (j - 1) else if j = k + 1 then σ
  else if j ≤ 2 * k + 1 then d j else -1

/-- The coordinates of an ordinary path product with the same characteristic polynomial as a
pattern product: `u_j + u_(j+1) + δ [j = k + 1]` for `u = patU k d σ`. -/
def patCoord (k : ℕ) (d : ℕ → R) (σ δ : R) : ℕ → R := fun j =>
  patU k d σ j + patU k d σ (j + 1) + if j = k + 1 then δ else 0

theorem patU_succ_of_lt {k : ℕ} {d : ℕ → R} {σ : R} {i : ℕ} (hi : i < k) :
    patU k d σ (i + 1) = d i := by
  unfold patU
  rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel]

theorem patU_right {k : ℕ} {d : ℕ → R} {σ : R} {i : ℕ} (hi : i < k) :
    patU k d σ (k + 2 + i) = d (k + 2 + i) := by
  unfold patU
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

theorem qPoly_patU (k : ℕ) (d : ℕ → R) (σ : R) :
    qPoly k (patU k d σ) =
      X ^ (2 * k + 2) + (∑ i ∈ Finset.range k, (-1) ^ i * C (d i) * X ^ (2 * k + 1 - i)) +
        (-1) ^ (k + 1) * C (-σ) * X ^ (k + 1) +
        (∑ i ∈ Finset.range k, (-1) ^ (k + 1 + i) * C (d (k + 2 + i)) * X ^ (k - i)) + 1 := by
  rw [qPoly, show 2 * k + 3 = (k + 2) + (k + 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ]
  have e0 : patU k d σ 0 = -1 := by simp [patU]
  have e1 : patU k d σ (k + 1) = σ := by simp [patU]
  have etop : patU k d σ (k + 2 + k) = -1 := by
    simp only [patU]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  have hl : ∀ i ∈ Finset.range k, (-1) ^ (i + 1) * C (patU k d σ (i + 1)) *
      X ^ (2 * k + 2 - (i + 1)) = -((-1) ^ i * C (d i) * X ^ (2 * k + 1 - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : patU k d σ (i + 1) = d i := by
      simp only [patU]
      rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel]
    rw [this, show 2 * k + 2 - (i + 1) = 2 * k + 1 - i by omega]
    ring
  have hr : ∀ i ∈ Finset.range k, (-1) ^ (k + 2 + i) * C (patU k d σ (k + 2 + i)) *
      X ^ (2 * k + 2 - (k + 2 + i)) = -((-1) ^ (k + 1 + i) * C (d (k + 2 + i)) * X ^ (k - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : patU k d σ (k + 2 + i) = d (k + 2 + i) := by
      simp only [patU]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega)]
    rw [this, show 2 * k + 2 - (k + 2 + i) = k - i by omega]
    ring
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr, Finset.sum_neg_distrib,
    Finset.sum_neg_distrib, e0, e1, etop, show 2 * k + 2 - (k + 2 + k) = 0 by omega]
  simp only [pow_zero, Nat.sub_zero, mul_one, map_neg, map_one]
  rw [show 2 * k + 2 - (k + 1) = k + 1 by omega,
    (Even.neg_one_pow ⟨k + 1, by ring⟩ : (-1 : R[X]) ^ (k + 2 + k) = 1)]
  ring

theorem ordPoly_patCoord (k : ℕ) (d : ℕ → R) (σ δ : R) :
    ordPoly k (patCoord k d σ δ) =
      (X - 1) * qPoly k (patU k d σ) + (-1) ^ (k + 1) * C δ * X ^ (k + 1) := by
  apply ordPoly_shift
  · simp [patU]
  · simp only [patU]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]

/-- **Characteristic polynomial of a pattern product as an ordinary one.** Under the hypotheses
of `charpoly_pathMat_pattern`, the characteristic polynomial of `pathMat k c β` is that of the
ordinary path product with coordinates `patCoord k c (-β₀₀) (β₀₁ β₁₀)`. -/
theorem charpoly_pathMat_pattern_eq_ordPoly (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R)
    (h12 : β 1 2 = 0) (h22 : β 2 2 = 0) (h11 : β 1 1 = 1) (h21 : β 2 1 = 0)
    (h0220 : β 0 2 * β 2 0 = -1) :
    (pathMat k c β).charpoly = ordPoly k (patCoord k c (-β 0 0) (β 0 1 * β 1 0)) := by
  rw [charpoly_pathMat_pattern k c β h12 h22 h11 h21 h0220, ordPoly_patCoord, qPoly_patU,
    neg_neg, map_mul]
  ring

/-! ### The coordinate map is bijective -/

theorem sum_alternating_add_succ (u : ℕ → R) (N : ℕ) :
    ∑ j ∈ Finset.range N, (-1) ^ j * (u j + u (j + 1)) = u 0 - (-1) ^ N * u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- The alternating sum of the pattern coordinates is `(-1)^(k+1) δ`. -/
theorem sum_alternating_patCoord (k : ℕ) (d : ℕ → R) (σ δ : R) :
    ∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * patCoord k d σ δ j = (-1) ^ (k + 1) * δ := by
  have hs : ∀ j, (-1 : R) ^ j * patCoord k d σ δ j = (-1) ^ j * (patU k d σ j +
      patU k d σ (j + 1)) + (-1) ^ j * (if j = k + 1 then δ else 0) := fun j => by
    simp only [patCoord]
    ring
  rw [Finset.sum_congr rfl fun j _ => hs j, Finset.sum_add_distrib, sum_alternating_add_succ]
  rw [Finset.sum_eq_single (k + 1)]
  · have e0 : patU k d σ 0 = -1 := by simp [patU]
    have etop : patU k d σ (2 * k + 2) = -1 := by
      simp only [patU]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
    rw [e0, etop, ite_eq_left rfl,
      (Even.neg_one_pow ⟨k + 1, by ring⟩ : (-1 : R) ^ (2 * k + 2) = 1)]
    ring
  · intro j _ hj
    rw [ite_eq_right hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- **Injectivity.** The pattern coordinates determine `δ`, `σ` and the relevant `d_i`. -/
theorem eq_of_patCoord_eq {k : ℕ} {d d' : ℕ → R} {σ σ' δ δ' : R}
    (h : ∀ j < 2 * k + 2, patCoord k d σ δ j = patCoord k d' σ' δ' j) :
    δ = δ' ∧ σ = σ' ∧ (∀ i < k, d i = d' i) ∧ (∀ i < k, d (k + 2 + i) = d' (k + 2 + i)) := by
  have hδ : δ = δ' := by
    have h1 := sum_alternating_patCoord k d σ δ
    rw [Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)],
      sum_alternating_patCoord] at h1
    have h2 := congrArg (fun r => (-1) ^ (k + 1) * r) h1
    simp only [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at h2
    exact h2.symm
  subst hδ
  have hu : ∀ j ≤ 2 * k + 2, patU k d σ j = patU k d' σ' j := by
    intro j hj
    induction j with
    | zero => simp [patU]
    | succ j ih =>
      have := h j (by omega)
      simp only [patCoord] at this
      rw [ih (by omega)] at this
      linear_combination this
  refine ⟨rfl, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := hu (k + 1) (by omega)
    simpa [patU] using this
  · have := hu (i + 1) (by omega)
    rwa [patU_succ_of_lt hi, patU_succ_of_lt hi] at this
  · have := hu (k + 2 + i) (by omega)
    rwa [patU_right hi, patU_right hi] at this

/-- The sequence solving `u_(j+1) = γ_j - u_j - δ [j = k + 1]` with `u_0 = -1`. -/
def solveU (k : ℕ) (γ : ℕ → R) (δ : R) : ℕ → R
  | 0 => -1
  | j + 1 => γ j - solveU k γ δ j - if j = k + 1 then δ else 0

/-- **Surjectivity.** Every family of coordinates is the coordinate family of a pattern
product, with `δ = (-1)^(k+1) Σ_{j<2k+2} (-1)^j γ_j`. -/
theorem exists_patCoord_eq (k : ℕ) (γ : ℕ → R) :
    ∃ (d : ℕ → R) (σ : R), ∀ j < 2 * k + 2,
      patCoord k d σ ((-1) ^ (k + 1) * ∑ i ∈ Finset.range (2 * k + 2), (-1) ^ i * γ i) j = γ j := by
  set δ := (-1) ^ (k + 1) * ∑ i ∈ Finset.range (2 * k + 2), (-1) ^ i * γ i
  set u := solveU k γ δ
  refine ⟨fun j => if j < k then u (j + 1) else u j, u (k + 1), ?_⟩
  have hrec : ∀ j, u j + u (j + 1) + (if j = k + 1 then δ else 0) = γ j := by
    intro j
    change u j + (γ j - u j - _) + _ = _
    ring
  have htop : u (2 * k + 2) = -1 := by
    have h1 := sum_alternating_add_succ u (2 * k + 2)
    have h2 : ∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * (u j + u (j + 1)) =
        ∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * γ j - (-1) ^ (k + 1) * δ := by
      have hγ : ∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * γ j =
          ∑ j ∈ Finset.range (2 * k + 2), ((-1) ^ j * (u j + u (j + 1)) +
            (-1) ^ j * (if j = k + 1 then δ else 0)) :=
        Finset.sum_congr rfl fun j _ => by rw [← hrec j]; ring
      have hδ' : ∑ j ∈ Finset.range (2 * k + 2), (-1 : R) ^ j * (if j = k + 1 then δ else 0) =
          (-1) ^ (k + 1) * δ := by
        rw [Finset.sum_eq_single (k + 1) (fun j _ hj => by rw [ite_eq_right hj, mul_zero])
          (fun h => absurd (Finset.mem_range.2 (by omega)) h), ite_eq_left rfl]
      rw [hγ, Finset.sum_add_distrib, hδ']
      ring
    rw [h2, (Even.neg_one_pow ⟨k + 1, by ring⟩ : (-1 : R) ^ (2 * k + 2) = 1), one_mul] at h1
    have h0 : u 0 = -1 := rfl
    rw [h0] at h1
    have h3 : (-1 : R) ^ (k + 1) * δ = ∑ i ∈ Finset.range (2 * k + 2), (-1) ^ i * γ i := by
      simp only [δ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    rw [h3, sub_self] at h1
    linear_combination h1
  have hpat : ∀ j ≤ 2 * k + 2, patU k (fun j => if j < k then u (j + 1) else u j) (u (k + 1)) j =
      u j := by
    intro j hj
    simp only [patU]
    by_cases h0 : j = 0
    · rw [ite_eq_left h0, h0]; rfl
    rw [ite_eq_right h0]
    by_cases h1 : j ≤ k
    · rw [ite_eq_left h1, ite_eq_left (by omega), Nat.sub_add_cancel (by omega)]
    rw [ite_eq_right h1]
    by_cases h2 : j = k + 1
    · rw [ite_eq_left h2, h2]
    rw [ite_eq_right h2]
    by_cases h3 : j ≤ 2 * k + 1
    · rw [ite_eq_left h3, ite_eq_right (by omega)]
    · rw [ite_eq_right h3, show j = 2 * k + 2 by omega, htop]
  intro j hj
  simp only [patCoord]
  rw [hpat j (by omega), hpat (j + 1) (by omega), hrec]

end Langlands.LinearAlgebra.PathCoxeter
