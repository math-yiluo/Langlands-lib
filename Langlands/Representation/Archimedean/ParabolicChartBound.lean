import Langlands.Representation.Archimedean.MaximalParabolicIntegration

/-!
# Growth of principal-series functions along the opposite unipotent radical of `P_{m,1}`
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ParabolicChartBound

open MaximalParabolicIntegration GramFormula Langlands.GeneralLinear

variable {m : ℕ}

/-! ## Partial square sums -/

/-- `r_l(x) = 1 + ∑_{j < l} x_j²`. -/
def partialSq (x : Fin m → ℝ) (l : ℕ) : ℝ :=
  1 + ∑ j : Fin m, if (j : ℕ) < l then x j ^ 2 else 0

theorem partialSq_zero (x : Fin m → ℝ) : partialSq x 0 = 1 := by
  simp [partialSq]

theorem one_le_partialSq (x : Fin m → ℝ) (l : ℕ) : 1 ≤ partialSq x l := by
  unfold partialSq
  have : 0 ≤ ∑ j : Fin m, (if (j : ℕ) < l then x j ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

theorem partialSq_pos (x : Fin m → ℝ) (l : ℕ) : 0 < partialSq x l :=
  lt_of_lt_of_le one_pos (one_le_partialSq x l)

theorem one_add_sq_le_partialSq (x : Fin m → ℝ) (l : Fin m) :
    1 + x l ^ 2 ≤ partialSq x ((l : ℕ) + 1) := by
  unfold partialSq
  have h := Finset.single_le_sum
    (f := fun j : Fin m => if (j : ℕ) < (l : ℕ) + 1 then x j ^ 2 else 0)
    (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ l)
  have h2 : (if (l : ℕ) < (l : ℕ) + 1 then x l ^ 2 else 0) = x l ^ 2 :=
    ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self _) h
  simp only [h2] at h
  linarith

theorem partialSq_smul_le {s : ℝ} (hs : |s| ≤ 1) (x : Fin m → ℝ) (l : ℕ) :
    partialSq (s • x) l ≤ partialSq x l := by
  unfold partialSq
  have hs2 : s ^ 2 ≤ 1 := by
    have := abs_nonneg s
    nlinarith [sq_abs s]
  have h : (∑ j : Fin m, if (j : ℕ) < l then (s • x) j ^ 2 else 0) ≤
      ∑ j : Fin m, if (j : ℕ) < l then x j ^ 2 else 0 := by
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      nlinarith [sq_nonneg (x j)]
    · exact le_rfl
  linarith

/-! ## Gram determinants of the chart matrices -/

/-- The entries of `x` at positions `≥ l`. -/
def tailVec (l : ℕ) (x : Fin m → ℝ) : Fin m → ℝ := fun j => if l ≤ (j : ℕ) then x j else 0

theorem Jmat_castSucc (r : Fin (m + 1) → ℝ) (i : Fin m) :
    Jmat r i.castSucc = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i.castSucc := by
  funext j
  simp [Jmat]

theorem Jmat_last (r : Fin (m + 1) → ℝ) : Jmat r (Fin.last m) = r := by
  funext j
  simp [Jmat]

theorem sum_one_mul (a : Fin (m + 1)) (f : Fin (m + 1) → ℝ) :
    ∑ j, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) a j * f j = f a := by
  simp [Matrix.one_apply]

theorem paddedGram_chart {l : ℕ} (hl : l ≤ m) (x : Fin m → ℝ) :
    paddedGram l (Jmat (Fin.snoc x 1 : Fin (m + 1) → ℝ)) =
      Jmat (Fin.snoc (tailVec l x) 1 : Fin (m + 1) → ℝ) *
        (Jmat (Fin.snoc (tailVec l x) (partialSq x l) : Fin (m + 1) → ℝ))ᵀ := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [paddedGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  refine Fin.lastCases ?_ (fun p' => ?_) p <;> refine Fin.lastCases ?_ (fun q' => ?_) q
  · rw [ite_eq_left (by simp [hl])]
    simp only [Jmat_last]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    unfold partialSq tailVec
    have h : ∀ j : Fin m, x j * x j = (if l ≤ (j : ℕ) then x j else 0) *
        (if l ≤ (j : ℕ) then x j else 0) + (if (j : ℕ) < l then x j ^ 2 else 0) := by
      intro j
      by_cases hj : l ≤ (j : ℕ)
      · rw [ite_eq_left hj, ite_eq_right (by omega)]
        ring
      · rw [ite_eq_right hj, ite_eq_left (by omega)]
        ring
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib]
    simp only [one_mul, mul_one]
    ring
  · simp only [Jmat_last, Jmat_castSucc]
    by_cases hq : l ≤ (q' : ℕ)
    · rw [ite_eq_left (by simp [hq, hl])]
      simp [mul_comm, sum_one_mul, tailVec, hq]
    · rw [ite_eq_right (by simp [hq])]
      simp [Matrix.one_apply, tailVec, hq]
      exact fun h => Fin.castSucc_ne_last q' h.symm
  · simp only [Jmat_last, Jmat_castSucc, sum_one_mul]
    by_cases hp : l ≤ (p' : ℕ)
    · rw [ite_eq_left (by simp [hp, hl])]
      simp [tailVec, hp]
    · rw [ite_eq_right (by simp [hp])]
      simp [tailVec, hp, Fin.castSucc_ne_last]
  · simp only [Jmat_castSucc, sum_one_mul]
    split_ifs <;> simp [Matrix.one_apply, eq_comm]

theorem gram_chart {l : ℕ} (hl : l ≤ m) (x : Fin m → ℝ) :
    gram l (Jmat (Fin.snoc x 1 : Fin (m + 1) → ℝ)) = partialSq x l := by
  rw [gram, paddedGram_chart hl, Matrix.det_mul, Matrix.det_transpose, det_Jmat, det_Jmat]
  simp

theorem paddedGram_mul_orthogonal {n : ℕ} (y κ : Matrix (Fin n) (Fin n) ℝ) (hκ : κ * κᵀ = 1)
    (l : ℕ) : paddedGram l (y * κ) = paddedGram l y := by
  ext p q
  simp only [paddedGram, Matrix.of_apply, mul_mul_transpose hκ]

theorem gram_mul_orthogonal {n : ℕ} (y κ : Matrix (Fin n) (Fin n) ℝ) (hκ : κ * κᵀ = 1)
    (l : ℕ) : gram l (y * κ) = gram l y := by
  rw [gram, gram, paddedGram_mul_orthogonal y κ hκ]

theorem gram_diagonal_mul {n : ℕ} (a : Fin n → ℝ) (u κ : Matrix (Fin n) (Fin n) ℝ)
    (hu : u.IsUpperTriangular) (hu1 : ∀ i, u i i = 1) (hκ : κ * κᵀ = 1) (l : ℕ) :
    gram l (Matrix.diagonal a * u * κ) = (∏ j : Fin n, if l ≤ (j : ℕ) then a j else 1) ^ 2 := by
  have hb : (Matrix.diagonal a * u).IsUpperTriangular := (Matrix.blockTriangular_diagonal a).mul hu
  rw [gram_mul hb hκ, diagonalTail]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul, hu1, mul_one]

/-! ## Summation by parts -/

theorem sum_mul_eq_sum_sub {t : Fin (m + 1) → ℝ} {σ : ℕ → ℝ} {T : ℕ → ℝ}
    (hT : ∀ l : ℕ, T l = ∑ j : Fin (m + 1), if l ≤ (j : ℕ) then t j else 0) (hT0 : T 0 = 0) :
    ∑ l : Fin (m + 1), σ l * t l = ∑ l : Fin m, (σ ((l : ℕ) + 1) - σ l) * T ((l : ℕ) + 1) := by
  have hTlast : T (m + 1) = 0 := by
    rw [hT]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)
  have ht : ∀ l : Fin (m + 1), t l = T l - T ((l : ℕ) + 1) := by
    intro l
    rw [hT, hT, ← Finset.sum_sub_distrib]
    have h : ∀ j : Fin (m + 1), ((if (l : ℕ) ≤ (j : ℕ) then t j else 0) -
        if (l : ℕ) + 1 ≤ (j : ℕ) then t j else 0) = if j = l then t j else 0 := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [ite_eq_left le_rfl, ite_eq_right (by omega), ite_eq_left rfl, sub_zero]
      · rw [ite_eq_right hj]
        have hjv : (j : ℕ) ≠ (l : ℕ) := fun h => hj (Fin.ext h)
        by_cases hlj : (l : ℕ) ≤ (j : ℕ)
        · rw [ite_eq_left hlj, ite_eq_left (by omega), sub_self]
        · rw [ite_eq_right hlj, ite_eq_right (by omega), sub_self]
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq']
    simp
  calc ∑ l : Fin (m + 1), σ l * t l
      = ∑ l : Fin (m + 1), σ l * T l - ∑ l : Fin (m + 1), σ l * T ((l : ℕ) + 1) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by rw [ht l]; ring
    _ = ∑ l : Fin m, (σ ((l : ℕ) + 1) - σ l) * T ((l : ℕ) + 1) := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        simp only [Fin.val_zero, hT0, mul_zero, zero_add, Fin.val_succ, Fin.val_castSucc,
          Fin.val_last, hTlast, add_zero]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring

/-! ## The growth bound -/

section Bound

variable {F : Langlands.GeneralLinear (m + 1) ℝ → ℂ} {c : (Fin (m + 1) → ℝˣ) → ℂ} {σ : ℕ → ℝ}

theorem prod_tail_sq_eq (x : Fin m → ℝ) (κ : Langlands.GeneralLinear (m + 1) ℝ)
    (hκ : κ ∈ unitaryCompact ℝ (m + 1)) (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
    (k : Langlands.GeneralLinear (m + 1) ℝ) (hk : k ∈ unitaryCompact ℝ (m + 1))
    (hg : chartGL x * κ = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * k) {l : ℕ} (hl : l ≤ m) :
    (∏ j : Fin (m + 1), if l ≤ (j : ℕ) then (a j : ℝ) else 1) ^ 2 = partialSq x l := by
  have hκ' : (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * (κ : Matrix _ _ ℝ)ᵀ = 1 :=
    OrthogonalLastRowIntegral.mul_transpose_eq_one ⟨κ, hκ⟩
  have hk' : (k : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * (k : Matrix _ _ ℝ)ᵀ = 1 :=
    OrthogonalLastRowIntegral.mul_transpose_eq_one ⟨k, hk⟩
  have hval := congrArg (fun g : Langlands.GeneralLinear (m + 1) ℝ =>
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) hg
  simp only [Units.val_mul, Iwasawa.diagonalUnits_val] at hval
  have h1 := congrArg (gram l) hval
  rw [chartGL, JGL_val, gram_mul_orthogonal _ _ hκ', gram_chart hl,
    gram_diagonal_mul _ _ _ u.2.1 u.2.2 hk'] at h1
  exact h1.symm

/-- **Growth along the chart.** If `F(diag(a) u g) = c(a) F(g)` with `‖c(a)‖ = ∏ |a_l|^{σ_l}`
and `‖F‖ ≤ C` on `O(m+1)`, then
`‖F(J(x,1) κ)‖ ≤ C ∏_{l<m} r_{l+1}(x)^{(σ_{l+1} - σ_l)/2}` for `κ ∈ O(m+1)`. -/
theorem norm_le_chart
    (hF : ∀ (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
      (g : Langlands.GeneralLinear (m + 1) ℝ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℝ) *
        (u : Langlands.GeneralLinear (m + 1) ℝ) * g) = c a * F g)
    (hc : ∀ a, ‖c a‖ = ∏ l : Fin (m + 1), |(a l : ℝ)| ^ σ l)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ (m + 1), ‖F k‖ ≤ C)
    (x : Fin m → ℝ) {κ : Langlands.GeneralLinear (m + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    ‖F (chartGL x * κ)‖ ≤
      C * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ ((σ ((l : ℕ) + 1) - σ l) / 2) := by
  obtain ⟨a, u, k, hk, hg⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact
    (chartGL x * κ)
  rw [hg, hF, norm_mul, hc, mul_comm]
  have hprod : ∏ l : Fin (m + 1), |(a l : ℝ)| ^ σ l =
      ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ ((σ ((l : ℕ) + 1) - σ l) / 2) := by
    have ha : ∀ l, 0 < |(a l : ℝ)| := fun l => abs_pos.mpr (a l).ne_zero
    set T : ℕ → ℝ := fun l => ∑ j : Fin (m + 1),
      if l ≤ (j : ℕ) then Real.log |(a j : ℝ)| else 0 with hTdef
    have hT : ∀ l : ℕ, l ≤ m → T l = Real.log (partialSq x l) / 2 := by
      intro l hl
      have h := prod_tail_sq_eq x κ hκ a u k hk hg hl
      rw [← h, Real.log_pow, ← Real.log_abs, Finset.abs_prod, Real.log_prod]
      · rw [hTdef]
        simp only
        push_cast
        rw [mul_div_cancel_left₀ _ two_ne_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      · intro j _
        split_ifs
        · exact (ha j).ne'
        · simp
    have hT0 : T 0 = 0 := by rw [hT 0 (Nat.zero_le _), partialSq_zero, Real.log_one, zero_div]
    have hsum := sum_mul_eq_sum_sub (t := fun l => Real.log |(a l : ℝ)|) (σ := σ) (T := T)
      (fun l => rfl) hT0
    rw [← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (ha l) _),
      ← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (partialSq_pos x _) _),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (ha l) _).ne'),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (partialSq_pos x _) _).ne')]
    congr 1
    simp only [Real.log_rpow (ha _), Real.log_rpow (partialSq_pos x _)]
    rw [show (∑ l : Fin (m + 1), σ l * Real.log |(a l : ℝ)|) = _ from hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hT _ (by have := l.isLt; omega)]
    ring
  rw [hprod]
  exact mul_le_mul_of_nonneg_right (hC k hk)
    (Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (partialSq_pos x _) _).le)

end Bound

/-! ## Integrability of the dominating function -/

theorem integrable_one_add_sq_rpow {γ : ℝ} (hγ : γ < -1 / 2) :
    Integrable fun t : ℝ => (1 + t ^ 2) ^ γ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := -2 * γ)
    (by rw [Module.finrank_self]; push_cast; linarith)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

theorem integrable_prod_one_add_sq_rpow {γ : Fin m → ℝ} (hγ : ∀ l, γ l < -1 / 2) :
    Integrable fun x : Fin m → ℝ => ∏ l, (1 + x l ^ 2) ^ γ l := by
  have h := Integrable.fintype_prod (f := fun l (t : ℝ) => (1 + t ^ 2) ^ γ l)
    (μ := fun _ => (volume : Measure ℝ)) fun l => integrable_one_add_sq_rpow (hγ l)
  rwa [← volume_pi] at h

/-! ## Domination -/

theorem prod_partialSq_rpow_le {x : Fin m → ℝ} {ε : Fin m → ℝ} (hε : ∀ l, ε l ≤ 0) :
    ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ ε l ≤ ∏ l : Fin m, (1 + x l ^ 2) ^ ε l :=
  Finset.prod_le_prod₀ (fun l _ => (Real.rpow_pos_of_pos (partialSq_pos x _) _).le)
    fun l _ => Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_sq_le_partialSq x l) (hε l)

/-- The product of the bounds for a pair of dual functions, the first one evaluated at the
contracted point `s • x` with `|s| ≤ 1`, is dominated by `∏ (1 + x_l²)^{max(ε^h_l, -1)}`. -/
theorem prod_rpow_mul_prod_rpow_le {x : Fin m → ℝ} {s : ℝ} (hs : |s| ≤ 1) {εu εh : Fin m → ℝ}
    (hsum : ∀ l, εu l + εh l = -1) (hneg : ∀ l, εh l < 0) :
    (∏ l : Fin m, partialSq (s • x) ((l : ℕ) + 1) ^ εu l) *
        ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ εh l ≤
      ∏ l : Fin m, (1 + x l ^ 2) ^ max (εh l) (-1) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun l _ => mul_nonneg
    (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le
    (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le) fun l _ => ?_
  set A := partialSq (s • x) ((l : ℕ) + 1)
  set B := partialSq x ((l : ℕ) + 1)
  have hA : 1 ≤ A := one_le_partialSq _ _
  have hB : 1 ≤ B := one_le_partialSq _ _
  have hAB : A ≤ B := partialSq_smul_le hs x _
  have hmax : max (εh l) (-1) ≤ 0 := max_le (hneg l).le (by norm_num)
  have h1 : A ^ εu l * B ^ εh l ≤ B ^ max (εh l) (-1) := by
    by_cases hu : 0 ≤ εu l
    · calc A ^ εu l * B ^ εh l ≤ B ^ εu l * B ^ εh l :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hAB hu)
              (Real.rpow_pos_of_pos (by linarith) _).le
        _ = B ^ (-1 : ℝ) := by rw [← Real.rpow_add (by linarith), hsum l]
        _ ≤ B ^ max (εh l) (-1) := Real.rpow_le_rpow_of_exponent_le hB (le_max_right _ _)
    · calc A ^ εu l * B ^ εh l ≤ 1 * B ^ εh l :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith))
              (Real.rpow_pos_of_pos (by linarith) _).le
        _ = B ^ εh l := one_mul _
        _ ≤ B ^ max (εh l) (-1) := Real.rpow_le_rpow_of_exponent_le hB (le_max_left _ _)
  exact h1.trans (Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_sq_le_partialSq x l) hmax)

end ParabolicChartBound

open ParabolicChartBound MaximalParabolicIntegration Langlands.GeneralLinear

/-- **Statement (growth along the opposite unipotent radical of `P_{m,1}`).** Let
`F : GL_{m+1}(ℝ) → ℂ` satisfy `F(diag(a) u g) = c(a) F(g)` for all `a ∈ (ℝˣ)^{m+1}`, upper
unipotent `u` and `g`, where `‖c(a)‖ = ∏_l |a_l|^{σ_l}`, and let `‖F‖ ≤ C` on `O(m+1)`. Then for
every `x ∈ ℝ^m` and `κ ∈ O(m+1)`,
`‖F(J(x,1) κ)‖ ≤ C ∏_{l<m} (1 + ∑_{j ≤ l} x_j²)^{(σ_{l+1} - σ_l)/2}`,
where `J(x,1)` is the identity matrix with last row `(x, 1)`. -/
def ParabolicChartBoundStatement : Prop :=
  ∀ (m : ℕ) (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ) (c : (Fin (m + 1) → ℝˣ) → ℂ)
    (σ : ℕ → ℝ),
    (∀ (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
      (g : Langlands.GeneralLinear (m + 1) ℝ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℝ) *
        (u : Langlands.GeneralLinear (m + 1) ℝ) * g) = c a * F g) →
    (∀ a, ‖c a‖ = ∏ l : Fin (m + 1), |(a l : ℝ)| ^ σ l) →
    ∀ C : ℝ, (∀ k ∈ unitaryCompact ℝ (m + 1), ‖F k‖ ≤ C) →
      ∀ (x : Fin m → ℝ) (κ : Langlands.GeneralLinear (m + 1) ℝ), κ ∈ unitaryCompact ℝ (m + 1) →
        ‖F (chartGL x * κ)‖ ≤
          C * ∏ l : Fin m, (1 + ∑ j : Fin m, if (j : ℕ) < (l : ℕ) + 1 then x j ^ 2 else 0) ^
            ((σ ((l : ℕ) + 1) - σ l) / 2)

theorem parabolicChartBound : ParabolicChartBoundStatement :=
  fun _ _ _ _ hF hc _ hC _ _ hκ => norm_le_chart hF hc hC _ hκ

end Langlands.Archimedean
