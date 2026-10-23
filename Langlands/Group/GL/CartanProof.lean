import Langlands.Group.GL.CartanStatement

/-!
# Proof of the Cartan decomposition over a discretely valued field

Existence is proved by induction on the rank: integral permutations move an entry of largest
valuation to the last diagonal place, integral column and row operations clear the rest of the
last row and column, and the induction hypothesis is applied to the remaining block.
Uniqueness compares, for each `k`, the largest valuation of the `(m - k)`-minors, which integral
factors cannot increase; for an antitone exponent it is `v ϖ` to the sum of the exponents with
index at least `k`.
-/

noncomputable section

namespace Langlands.GeneralLinear.Cartan

open Matrix Langlands.Conductor Iwasawa

universe uF uΓ

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀}

/-! ### Integral entries -/

theorem entry_mem_of_mem {m : ℕ} {k : Matrix.GeneralLinearGroup (Fin m) F}
    (hk : k ∈ integralRange v m) (i j : Fin m) : k i j ∈ v.integer := by
  obtain ⟨k, rfl⟩ := hk
  exact (k i j).property

/-- Left multiplication by an integral matrix preserves an upper bound on the entries. -/
theorem entry_mul_left_le {m : ℕ} {P A : Matrix (Fin m) (Fin m) F} {γ : Γ₀}
    (hP : ∀ i j, P i j ∈ v.integer) (hA : ∀ i j, v (A i j) ≤ γ) (i j : Fin m) :
    v ((P * A) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le v fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((v.mem_integer_iff _).1 (hP i l)) (hA l j)

/-- Right multiplication by an integral matrix preserves an upper bound on the entries. -/
theorem entry_mul_right_le {m : ℕ} {A Q : Matrix (Fin m) (Fin m) F} {γ : Γ₀}
    (hQ : ∀ i j, Q i j ∈ v.integer) (hA : ∀ i j, v (A i j) ≤ γ) (i j : Fin m) :
    v ((A * Q) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le v fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_of_le_one (hA i l) ((v.mem_integer_iff _).1 (hQ l j))

/-! ### Minors -/

/-- Expansion of a minor of a product along the rows of the left factor. -/
theorem det_submatrix_mul {m r : ℕ} (P B : Matrix (Fin m) (Fin m) F) (f h : Fin r → Fin m) :
    ((P * B).submatrix f h).det =
      ∑ φ : Fin r → Fin m, (∏ s, P (f s) (φ s)) * (B.submatrix φ h).det := by
  have hM : (P * B).submatrix f h = fun s => ∑ l, P (f s) l • (B.submatrix id h) l := by
    ext s t
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hM]
  change (detRowAlternating : (Fin r → F) [⋀^Fin r]→ₗ[F] F).toMultilinearMap _ = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/-- The determinant of a matrix with integral entries is integral. -/
theorem det_mem_integer {r : ℕ} (M : Matrix (Fin r) (Fin r) F) (hM : ∀ i j, M i j ∈ v.integer) :
    M.det ∈ v.integer := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hM _ _)

/-- Left multiplication by an integral matrix preserves an upper bound on the `r`-minors. -/
theorem minor_mul_left_le {m r : ℕ} {P B : Matrix (Fin m) (Fin m) F} {γ : Γ₀}
    (hP : ∀ i j, P i j ∈ v.integer)
    (hB : ∀ f h : Fin r → Fin m, v (B.submatrix f h).det ≤ γ) (f h : Fin r → Fin m) :
    v ((P * B).submatrix f h).det ≤ γ := by
  rw [det_submatrix_mul]
  refine Valuation.map_sum_le v fun φ _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le
    ((v.mem_integer_iff _).1 (prod_mem fun s _ => hP _ _)) (hB φ h)

/-- Right multiplication by an integral matrix preserves an upper bound on the `r`-minors. -/
theorem minor_mul_right_le {m r : ℕ} {B Q : Matrix (Fin m) (Fin m) F} {γ : Γ₀}
    (hQ : ∀ i j, Q i j ∈ v.integer)
    (hB : ∀ f h : Fin r → Fin m, v (B.submatrix f h).det ≤ γ) (f h : Fin r → Fin m) :
    v ((B * Q).submatrix f h).det ≤ γ := by
  have := minor_mul_left_le (P := Qᵀ) (B := Bᵀ) (fun i j => hQ j i)
    (fun f h => by rw [← Matrix.transpose_submatrix, Matrix.det_transpose]; exact hB h f) h f
  rwa [← Matrix.transpose_mul, ← Matrix.transpose_submatrix, Matrix.det_transpose] at this

/-! ### Tail sums of exponents -/

/-- The sum of the entries of `a` with index at least `k`. -/
def tailSum {m : ℕ} (a : Fin m → ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => k ≤ j.val), a j

theorem apply_eq_tailSum_sub {m : ℕ} (a : Fin m → ℤ) (i : Fin m) :
    a i = tailSum a i - tailSum a (i + 1) := by
  simp only [tailSum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : j.val ≠ i.val := fun h => hj (Fin.ext h)
    split_ifs <;> omega
  · simp

theorem eq_of_tailSum_eq {m : ℕ} {a b : Fin m → ℤ} (h : ∀ k, tailSum a k = tailSum b k) :
    a = b := by
  funext i
  rw [apply_eq_tailSum_sub a i, apply_eq_tailSum_sub b i, h, h]

/-- The increasing enumeration of the indices at least `k`. -/
def tailIndex (m k : ℕ) (s : Fin (m - k)) : Fin m :=
  ⟨k + s, by have := s.isLt; omega⟩

theorem tailIndex_injective (m k : ℕ) : Function.Injective (tailIndex m k) := by
  intro s t h
  have := congrArg Fin.val h
  simp only [tailIndex] at this
  exact Fin.ext (by omega)

theorem image_tailIndex (m k : ℕ) :
    Finset.univ.image (tailIndex m k) = Finset.univ.filter (fun j : Fin m => k ≤ j.val) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨s, rfl⟩
    simp [tailIndex]
  · intro hj
    exact ⟨⟨j - k, by have := j.isLt; omega⟩, Fin.ext (by simp [tailIndex]; omega)⟩

theorem sum_tailIndex {m : ℕ} (a : Fin m → ℤ) (k : ℕ) :
    ∑ s, a (tailIndex m k s) = tailSum a k := by
  rw [tailSum, ← image_tailIndex, Finset.sum_image fun x _ y _ h => tailIndex_injective m k h]

/-- A sum over a finset is at most a sum over another finset of the same size whose values
dominate. -/
theorem sum_le_sum_of_card_eq {ι : Type*} (s t : Finset ι) (f : ι → ℤ) (hc : s.card = t.card)
    (h : ∀ x ∈ s, ∀ y ∈ t, f x ≤ f y) : ∑ x ∈ s, f x ≤ ∑ y ∈ t, f y := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · rw [Finset.card_empty, Finset.card_eq_zero] at hc
    simp [hc]
  · obtain ⟨y0, hy0, hmin⟩ := Finset.exists_min_image t f ht
    calc ∑ x ∈ s, f x ≤ s.card • f y0 :=
          Finset.sum_le_card_nsmul s f (f y0) fun x hx => h x hx y0 hy0
      _ = t.card • f y0 := by rw [hc]
      _ ≤ ∑ y ∈ t, f y := Finset.card_nsmul_le_sum t f (f y0) fun y hy => hmin y hy

/-- For antitone `b`, the tail sum is the smallest sum of `b` over `m - k` distinct indices. -/
theorem tailSum_le_sum {m : ℕ} {b : Fin m → ℤ} (hb : Antitone b) (k : ℕ)
    (f : Fin (m - k) → Fin m) (hf : Function.Injective f) :
    tailSum b k ≤ ∑ s, b (f s) := by
  classical
  set T := Finset.univ.filter (fun j : Fin m => k ≤ j.val) with hT
  set B := Finset.univ.image f with hB
  have hTc : T.card = m - k := by
    rw [hT, ← image_tailIndex, Finset.card_image_of_injective _ (tailIndex_injective m k),
      Finset.card_univ, Fintype.card_fin]
  have hBc : B.card = m - k := by
    rw [hB, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  rw [show ∑ s, b (f s) = ∑ j ∈ B, b j from
    (Finset.sum_image fun x _ y _ h => hf h).symm, tailSum, ← hT,
    ← Finset.sum_inter_add_sum_sdiff T B, ← Finset.sum_inter_add_sum_sdiff B T,
    Finset.inter_comm B T]
  refine add_le_add le_rfl (sum_le_sum_of_card_eq _ _ _ ?_ ?_)
  · have h1 := Finset.card_sdiff_add_card_inter T B
    have h2 := Finset.card_sdiff_add_card_inter B T
    rw [Finset.inter_comm B T] at h2
    omega
  · intro x hx y hy
    rw [Finset.mem_sdiff, hT, Finset.mem_filter] at hx
    rw [Finset.mem_sdiff, hT, Finset.mem_filter] at hy
    have : y.val < x.val := by
      have := hx.1.2
      have := hy.2
      simp only [Finset.mem_univ, true_and, not_le] at this
      omega
    exact hb this.le

/-! ### Minors of diagonal matrices -/

/-- A product of powers in `Γ₀` is the power with the summed exponent. -/
theorem prod_zpow_eq {ι : Type*} (s : Finset ι) {x : Γ₀} (hx : x ≠ 0) (n : ι → ℤ) :
    ∏ i ∈ s, x ^ n i = x ^ ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

theorem diagonal_submatrix_eq {m r : ℕ} (d : Fin m → F) (f h : Fin r → Fin m) :
    (diagonal d).submatrix f h = diagonal (d ∘ f) * (1 : Matrix (Fin m) (Fin m) F).submatrix f h := by
  ext s t
  simp [diagonal_apply, one_apply, Matrix.diagonal_mul]

/-- The `(m - k)`-minors of `ϖ ^ b` for antitone `b` have valuation at most
`v ϖ ^ tailSum b k`. -/
theorem minor_torus_le {m : ℕ} {ϖ : Fˣ} (hϖ : v (ϖ : F) < 1) {b : Fin m → ℤ} (hb : Antitone b)
    (k : ℕ) (f h : Fin (m - k) → Fin m) :
    v ((torus ϖ b).val.submatrix f h).det ≤ v (ϖ : F) ^ tailSum b k := by
  by_cases hf : Function.Injective f
  · rw [torus_val, diagonal_submatrix_eq, det_mul, det_diagonal, map_mul]
    refine mul_le_of_le_of_le_one ?_ ((v.mem_integer_iff _).1 (det_mem_integer _ ?_))
    · rw [map_prod]
      simp only [Function.comp_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
      rw [prod_zpow_eq _ (valuation_pos v ϖ).ne']
      exact (zpow_le_zpow_iff_right_of_lt_one₀ (valuation_pos v ϖ) hϖ).2
        (tailSum_le_sum hb k f hf)
    · intro i j
      rw [submatrix_apply, one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · obtain ⟨s, t, hst, hne⟩ : ∃ s t, f s = f t ∧ s ≠ t := by
      simp only [Function.Injective, not_forall] at hf
      obtain ⟨s, t, hst, hne⟩ := hf
      exact ⟨s, t, hst, hne⟩
    rw [Matrix.det_zero_of_row_eq hne (by funext j; simp [hst]), map_zero]
    exact zero_le

/-! ### Uniqueness -/

/-- If `ϖ ^ a = P ϖ ^ b Q` with integral `P`, `Q` and antitone `b`, then every tail sum of `b`
is at most the corresponding tail sum of `a`. -/
theorem tailSum_le_of_eq {m : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ) {a b : Fin m → ℤ}
    (hb : Antitone b) {P Q : Matrix (Fin m) (Fin m) F} (hP : ∀ i j, P i j ∈ v.integer)
    (hQ : ∀ i j, Q i j ∈ v.integer) (h : (torus ϖ a).val = P * (torus ϖ b).val * Q) (k : ℕ) :
    tailSum b k ≤ tailSum a k := by
  have hbound := minor_mul_right_le hQ (minor_mul_left_le hP (minor_torus_le hϖ.1 hb k))
    (tailIndex m k) (tailIndex m k)
  rw [← h, torus_val, submatrix_diagonal _ _ (tailIndex_injective m k), det_diagonal,
    map_prod] at hbound
  simp only [Function.comp_apply, Units.val_zpow_eq_zpow_val, map_zpow₀] at hbound
  rw [prod_zpow_eq _ (valuation_pos v ϖ).ne', sum_tailIndex] at hbound
  exact (zpow_le_zpow_iff_right_of_lt_one₀ (valuation_pos v ϖ) hϖ.1).1 hbound

/-- The antitone exponent of a Cartan decomposition is unique. -/
theorem exponent_unique {m : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ) {a b : Fin m → ℤ}
    (ha : Antitone a) (hb : Antitone b) {k₁ k₂ k₁' k₂' : Matrix.GeneralLinearGroup (Fin m) F}
    (hk₁ : k₁ ∈ integralRange v m) (hk₂ : k₂ ∈ integralRange v m)
    (hk₁' : k₁' ∈ integralRange v m) (hk₂' : k₂' ∈ integralRange v m)
    (h : k₁ * torus ϖ a * k₂ = k₁' * torus ϖ b * k₂') : a = b := by
  have e1 : torus ϖ a = (k₁⁻¹ * k₁') * torus ϖ b * (k₂' * k₂⁻¹) := by
    calc torus ϖ a = k₁⁻¹ * (k₁ * torus ϖ a * k₂) * k₂⁻¹ := by group
      _ = _ := by rw [h]; group
  have e2 : torus ϖ b = (k₁'⁻¹ * k₁) * torus ϖ a * (k₂ * k₂'⁻¹) := by
    calc torus ϖ b = k₁'⁻¹ * (k₁' * torus ϖ b * k₂') * k₂'⁻¹ := by group
      _ = _ := by rw [← h]; group
  apply eq_of_tailSum_eq
  intro k
  apply le_antisymm
  · exact tailSum_le_of_eq hϖ ha (entry_mem_of_mem (mul_mem (inv_mem hk₁') hk₁))
      (entry_mem_of_mem (mul_mem hk₂ (inv_mem hk₂'))) (by rw [e2]; rfl) k
  · exact tailSum_le_of_eq hϖ hb (entry_mem_of_mem (mul_mem (inv_mem hk₁) hk₁'))
      (entry_mem_of_mem (mul_mem hk₂' (inv_mem hk₂))) (by rw [e1]; rfl) k


/-! ### Permutation matrices -/

/-- The permutation matrix whose `i`-th row is the `σ i`-th standard row vector. -/
def permMat {m : ℕ} (σ : Equiv.Perm (Fin m)) : Matrix (Fin m) (Fin m) F :=
  (1 : Matrix (Fin m) (Fin m) F).submatrix σ id

theorem permMat_mul_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (M : Matrix (Fin m) (Fin m) F)
    (i j : Fin m) : (permMat σ * M : Matrix (Fin m) (Fin m) F) i j = M (σ i) j := by
  simp [permMat, Matrix.mul_apply, Matrix.one_apply]

theorem mul_permMat_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (M : Matrix (Fin m) (Fin m) F)
    (i j : Fin m) : (M * permMat σ : Matrix (Fin m) (Fin m) F) i j = M i (σ.symm j) := by
  simp [permMat, Matrix.mul_apply, Matrix.one_apply, ← Equiv.eq_symm_apply]

theorem permMat_mul_permMat_symm {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    permMat σ * permMat σ.symm = (1 : Matrix (Fin m) (Fin m) F) := by
  ext i j
  rw [permMat_mul_apply]
  simp [permMat, Matrix.one_apply]

/-- The permutation matrix of `σ` as an invertible matrix. -/
def permGL {m : ℕ} (σ : Equiv.Perm (Fin m)) : Matrix.GeneralLinearGroup (Fin m) F :=
  ofInverse (permMat σ) (permMat σ.symm) (permMat_mul_permMat_symm σ)
    (by simpa using permMat_mul_permMat_symm σ.symm)

theorem permGL_mul_mul_apply {m : ℕ} (σ τ : Equiv.Perm (Fin m))
    (g : Matrix.GeneralLinearGroup (Fin m) F) (i j : Fin m) :
    (permGL σ * g * permGL τ : Matrix.GeneralLinearGroup (Fin m) F) i j = g (σ i) (τ.symm j) := by
  change (permMat σ * g.val * permMat τ : Matrix (Fin m) (Fin m) F) i j = _
  rw [mul_permMat_apply, permMat_mul_apply]

theorem permMat_mem {m : ℕ} (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    permMat (F := F) σ i j ∈ v.integer := by
  simp only [permMat, submatrix_apply, id, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem permGL_mem {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    permGL (F := F) σ ∈ integralSubgroup v.integer n :=
  ofInverse_mem v _ _ _ _ (permMat_mem σ) (permMat_mem σ.symm)

/-! ### Existence -/

/-- Integral permutations move an entry of maximal valuation to the last diagonal place. -/
theorem exists_pivot {m : ℕ} (g : Matrix.GeneralLinearGroup (Fin (m + 1)) F) :
    ∃ p₁ ∈ integralSubgroup v.integer m, ∃ p₂ ∈ integralSubgroup v.integer m,
      (p₁ * g * p₂) (Fin.last m) (Fin.last m) ≠ 0 ∧
        ∀ i j, v ((p₁ * g * p₂) i j) ≤ v ((p₁ * g * p₂) (Fin.last m) (Fin.last m)) := by
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ
    (fun x : Fin (m + 1) × Fin (m + 1) => v (g x.1 x.2)) Finset.univ_nonempty
  refine ⟨permGL (Equiv.swap x.1 (Fin.last m)), permGL_mem _,
    permGL (Equiv.swap x.2 (Fin.last m)), permGL_mem _, ?_, ?_⟩
  · rw [permGL_mul_mul_apply, Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_right]
    intro h0
    apply GeneralLinearGroup.det_ne_zero g
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last m)
    intro j
    have hj := hx (Fin.last m, j) (Finset.mem_univ _)
    rw [h0, map_zero] at hj
    exact (Valuation.zero_iff v).1 (le_antisymm hj zero_le)
  · intro i j
    rw [permGL_mul_mul_apply, permGL_mul_mul_apply, Equiv.symm_swap, Equiv.swap_apply_right,
      Equiv.swap_apply_right]
    exact hx (_, _) (Finset.mem_univ _)

/-- With a dominant nonzero last entry, integral row operations clear the rest of the last
column without changing the last row. -/
theorem exists_clear_last_col {m : ℕ} (h : Matrix.GeneralLinearGroup (Fin (m + 1)) F)
    (hne : h (Fin.last m) (Fin.last m) ≠ 0)
    (hdom : ∀ i, v (h i (Fin.last m)) ≤ v (h (Fin.last m) (Fin.last m))) :
    ∃ k ∈ integralSubgroup v.integer m,
      (∀ i, i ≠ Fin.last m → (k * h) i (Fin.last m) = 0) ∧
        ∀ j, (k * h) (Fin.last m) j = h (Fin.last m) j := by
  set c : Fin (m + 1) → F := fun i => h i (Fin.last m) / h (Fin.last m) (Fin.last m) with hc
  set N := (lastRowClearing c)ᵀ with hN
  have hNN : N * N = 0 := by
    rw [hN, ← Matrix.transpose_mul, lastRowClearing_mul_self, Matrix.transpose_zero]
  have h1 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hNN]
    abel
  have h2 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hNN]
    abel
  have hcO : ∀ i, c i ∈ v.integer := fun i => div_mem_integer v hne (hdom i)
  have hNO : ∀ i j, N i j ∈ v.integer := by
    intro i j
    simp only [hN, Matrix.transpose_apply, lastRowClearing, Matrix.of_apply]
    split_ifs
    · exact hcO i
    · exact zero_mem _
  have hmem : ofInverse _ _ h1 h2 ∈ integralSubgroup v.integer m := by
    refine ofInverse_mem v _ _ h1 h2 ?_ ?_
    · intro i j
      rw [Matrix.sub_apply]
      exact sub_mem (by rw [Matrix.one_apply]; split_ifs <;> simp) (hNO i j)
    · intro i j
      rw [Matrix.add_apply]
      exact add_mem (by rw [Matrix.one_apply]; split_ifs <;> simp) (hNO i j)
  have hentry : ∀ i j, (ofInverse _ _ h1 h2 * h) i j =
      h i j - N i (Fin.last m) * h (Fin.last m) j := by
    intro i j
    change ((1 - N) * h.val) i j = _
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply,
      Finset.sum_eq_single (Fin.last m)]
    · intro l _ hl
      simp [hN, lastRowClearing, hl]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  refine ⟨ofInverse _ _ h1 h2, hmem, ?_, ?_⟩
  · intro i hi
    rw [hentry]
    simp only [hN, Matrix.transpose_apply, lastRowClearing, Matrix.of_apply, hi, ne_eq,
      not_false_eq_true, and_self, ite_true, hc]
    field_simp
    ring
  · intro j
    rw [hentry]
    simp [hN, lastRowClearing]

theorem mul_diagonalUnits_apply {m : ℕ} (b : Matrix.GeneralLinearGroup (Fin m) F)
    (d : Fin m → Fˣ) (i j : Fin m) : (b * diagonalUnits d) i j = b i j * (d j : F) := by
  change (b.val * (diagonalUnits d).val) i j = _
  rw [diagonalUnits_val, Matrix.mul_diagonal]

theorem diagonalUnits_mul_apply {m : ℕ} (d : Fin m → Fˣ)
    (b : Matrix.GeneralLinearGroup (Fin m) F) (i j : Fin m) :
    (diagonalUnits d * b) i j = (d i : F) * b i j := by
  change ((diagonalUnits d).val * b.val) i j = _
  rw [diagonalUnits_val, Matrix.diagonal_mul]

theorem antitone_snoc {m : ℕ} {mu : Fin m → ℤ} (hmu : Antitone mu) {e : ℤ}
    (he : ∀ i, e ≤ mu i) : Antitone (Fin.snoc mu e : Fin (m + 1) → ℤ) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using he i
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
    | cast i => simpa using hmu (Fin.castSucc_le_castSucc_iff.1 hij)

/-- Existence of a Cartan decomposition with antitone exponent. -/
theorem exists_cartan {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ) :
    ∀ (m : ℕ) (g : Matrix.GeneralLinearGroup (Fin m) F),
      ∃ lam : Fin m → ℤ, Antitone lam ∧
        ∃ k₁ ∈ integralRange v m, ∃ k₂ ∈ integralRange v m, g = k₁ * torus ϖ lam * k₂
  | 0, g => ⟨fun i => i.elim0, fun i => i.elim0, 1, one_mem _, 1, one_mem _, by
      apply Units.ext
      ext i
      exact i.elim0⟩
  | m + 1, g => by
    obtain ⟨p₁, hp₁, p₂, hp₂, hne, hdom⟩ := exists_pivot (v := v) g
    set g1 := p₁ * g * p₂ with hg1
    set p := g1 (Fin.last m) (Fin.last m) with hp
    obtain ⟨c₁, hc₁, hrow, hlast⟩ := exists_clear_last_row v g1 hne (fun j => hdom _ j)
    have hdom2 : ∀ i j, v ((g1 * c₁) i j) ≤ v p := fun i j =>
      entry_mul_right_le (A := g1.val) (Q := c₁.val)
        ((mem_integralSubgroup v.integer m c₁).1 hc₁).1 hdom i j
    rw [← hp] at hlast
    have hne2 : (g1 * c₁) (Fin.last m) (Fin.last m) ≠ 0 := by rw [hlast]; exact hne
    obtain ⟨k, hk, hcol, hrow'⟩ := exists_clear_last_col (v := v) (g1 * c₁) hne2
      (fun i => by rw [hlast]; exact hdom2 i _)
    set h3 := k * (g1 * c₁) with hh3
    have hrow3 : ∀ j, j ≠ Fin.last m → h3 (Fin.last m) j = 0 := fun j hj => by
      rw [hh3, hrow', hrow j hj]
    have hlast3 : h3 (Fin.last m) (Fin.last m) = p := by rw [hh3, hrow', hlast]
    have hdom3 : ∀ i j, v (h3 i j) ≤ v p := fun i j =>
      entry_mul_left_le (P := k.val) (A := (g1 * c₁).val)
        ((mem_integralSubgroup v.integer m k).1 hk).1 hdom2 i j
    set A : Matrix (Fin m) (Fin m) F := h3.val.submatrix Fin.castSucc Fin.castSucc with hA
    have hdet := det_eq_last_mul_det_castSucc h3.val hrow3
    have hAdet : A.det ≠ 0 := by
      intro h0
      apply GeneralLinearGroup.det_ne_zero h3
      rw [hdet, ← hA, h0, mul_zero]
    set A' := GeneralLinearGroup.mkOfDetNeZero A hAdet with hA'
    obtain ⟨mu, hmu, k₁, hk₁, k₂, hk₂, hAk⟩ := exists_cartan hϖ m A'
    obtain ⟨e, he⟩ := hϖ.2 p hne
    set pu : Fˣ := Units.mk0 p hne with hpu
    set ε : Fˣ := pu * (ϖ ^ e)⁻¹ with hε
    have hεv : v (ε : F) = 1 := by
      rw [hε, Units.val_mul, hpu, Units.val_mk0, map_mul, he, Units.val_inv_eq_inv_val,
        map_inv₀, Units.val_zpow_eq_zpow_val, map_zpow₀, mul_inv_cancel₀]
      exact zpow_ne_zero _ (valuation_pos v ϖ).ne'
    -- the last exponent is the smallest
    have hle : ∀ i, e ≤ mu i := by
      intro i
      have hT : torus ϖ mu = k₁⁻¹ * A' * k₂⁻¹ := by rw [hAk]; group
      have hbound : v ((torus ϖ mu) i i) ≤ v p := by
        rw [hT]
        refine entry_mul_right_le (A := (k₁⁻¹ * A').val) (Q := k₂⁻¹.val)
          (entry_mem_of_mem (inv_mem hk₂))
          (entry_mul_left_le (P := k₁⁻¹.val) (A := A'.val) (entry_mem_of_mem (inv_mem hk₁))
            (fun i j => ?_)) i i
        rw [hA', GeneralLinearGroup.val_mkOfDetNeZero, hA, submatrix_apply]
        exact hdom3 _ _
      rw [torus_val, diagonal_apply_eq, Units.val_zpow_eq_zpow_val, map_zpow₀, he] at hbound
      exact (zpow_le_zpow_iff_right_of_lt_one₀ (valuation_pos v ϖ) hϖ.1).1 hbound
    -- block decompositions
    have hI1 : h3 = rankInclusion 1 A' * diagonalUnits (Fin.snoc (1 : Fin m → Fˣ) pu) := by
      apply Units.ext
      ext i j
      rw [mul_diagonalUnits_apply]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [hlast3, hpu]
        | cast j => simp [hrow3 _ (Fin.castSucc_lt_last j).ne]
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [hcol _ (Fin.castSucc_lt_last i).ne]
        | cast j => simp [hA', hA]
    have hI2 : rankInclusion 1 k₂ * diagonalUnits (Fin.snoc (1 : Fin m → Fˣ) pu) =
        diagonalUnits (Fin.snoc (1 : Fin m → Fˣ) (ϖ ^ e)) *
          (rankInclusion 1 k₂ * diagonalUnits (Fin.snoc (1 : Fin m → Fˣ) ε)) := by
      apply Units.ext
      ext i j
      rw [mul_diagonalUnits_apply, ← mul_assoc, mul_diagonalUnits_apply,
        diagonalUnits_mul_apply]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [rankInclusion_last_last, Fin.snoc_last, hε, Units.val_mul, hpu, one_mul]
          rw [mul_one, mul_left_comm, Units.mul_inv, mul_one]
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simp
    have hI3 : rankInclusion 1 (torus ϖ mu) *
        diagonalUnits (Fin.snoc (1 : Fin m → Fˣ) (ϖ ^ e)) =
          torus ϖ (Fin.snoc mu e : Fin (m + 1) → ℤ) := by
      apply Units.ext
      ext i j
      rw [mul_diagonalUnits_apply, torus_val]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simp [diagonal_apply_ne _ (Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j =>
          simp only [rankInclusion_castSucc_castSucc, Fin.snoc_castSucc, Pi.one_apply,
            Units.val_one, mul_one, torus_val]
          by_cases hij : i = j
          · subst hij
            simp
          · rw [diagonal_apply_ne _ hij,
              diagonal_apply_ne _ (fun h => hij (Fin.castSucc_injective _ h))]
    have hD : ∀ i, v (((Fin.snoc (1 : Fin m → Fˣ) ε : Fin (m + 1) → Fˣ) i : Fˣ) : F) = 1 := by
      intro i
      induction i using Fin.lastCases with
      | last => simpa using hεv
      | cast i => simp
    have hg : g = p₁⁻¹ * k⁻¹ * h3 * c₁⁻¹ * p₂⁻¹ := by
      rw [hh3, hg1]
      group
    refine ⟨Fin.snoc mu e, antitone_snoc hmu hle,
      p₁⁻¹ * k⁻¹ * rankInclusion 1 k₁, ?_,
      rankInclusion 1 k₂ * diagonalUnits (Fin.snoc (1 : Fin m → Fˣ) ε) * c₁⁻¹ * p₂⁻¹, ?_, ?_⟩
    · rw [integralRange_succ]
      exact mul_mem (mul_mem (inv_mem hp₁) (inv_mem hk)) (rankInclusion_mem v hk₁)
    · rw [integralRange_succ]
      exact mul_mem (mul_mem (mul_mem (rankInclusion_mem v hk₂) (diagonalUnits_mem v _ hD))
        (inv_mem hc₁)) (inv_mem hp₂)
    · rw [hg, hI1, hAk, map_mul, map_mul,
        mul_assoc (rankInclusion 1 k₁ * rankInclusion 1 (torus ϖ mu)), hI2, ← hI3]
      simp only [mul_assoc]

/-! ### The Cartan decomposition -/

/-- The Cartan decomposition: every invertible matrix over a discretely valued field is an
integral matrix times a power of the uniformizer with a unique antitone exponent times an
integral matrix. -/
theorem cartanDecomposition : CartanDecompositionStatement.{uF, uΓ} := by
  intro F _ Γ₀ _ v ϖ hϖ m g
  obtain ⟨lam, hlam, k₁, hk₁, k₂, hk₂, hg⟩ := exists_cartan hϖ m g
  refine ⟨lam, ⟨hlam, k₁, hk₁, k₂, hk₂, hg⟩, ?_⟩
  rintro mu ⟨hmu, k₁', hk₁', k₂', hk₂', hg'⟩
  exact exponent_unique hϖ hmu hlam hk₁' hk₂' hk₁ hk₂ (hg'.symm.trans hg)

end Langlands.GeneralLinear.Cartan
