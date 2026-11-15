import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration

/-!
# Growth of complex principal-series functions along the opposite unipotent radical of `P_{m,1}`

If `F(diag(a) u g) = c(a) F(g)` with `‖c(a)‖ = ∏ |a_l|^{σ_l}` and `F` is bounded on `U(m+1)`, then
`‖F(J(x,1) κ)‖ ≤ C ∏_{l<m} (1 + ∑_{j ≤ l} |x_j|²)^{(σ_{l+1} - σ_l)/2}` for `κ ∈ U(m+1)`
(`ComplexParabolicChartBound.norm_le_chart`), together with the integrability and domination
estimates used for the partial Jacquet integral.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexParabolicChartBound

open ComplexMaximalParabolicIntegration Langlands.GeneralLinear

variable {m : ℕ}

/-! ## Partial square sums -/

/-- `r_l(x) = 1 + ∑_{j < l} |x_j|²`. -/
def partialSq (x : Fin m → ℂ) (l : ℕ) : ℝ :=
  1 + ∑ j : Fin m, if (j : ℕ) < l then ‖x j‖ ^ 2 else 0

theorem partialSq_zero (x : Fin m → ℂ) : partialSq x 0 = 1 := by
  simp [partialSq]

theorem one_le_partialSq (x : Fin m → ℂ) (l : ℕ) : 1 ≤ partialSq x l := by
  unfold partialSq
  have : 0 ≤ ∑ j : Fin m, (if (j : ℕ) < l then ‖x j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

theorem partialSq_pos (x : Fin m → ℂ) (l : ℕ) : 0 < partialSq x l :=
  lt_of_lt_of_le one_pos (one_le_partialSq x l)

theorem one_add_sq_le_partialSq (x : Fin m → ℂ) (l : Fin m) :
    1 + ‖x l‖ ^ 2 ≤ partialSq x ((l : ℕ) + 1) := by
  unfold partialSq
  have h := Finset.single_le_sum
    (f := fun j : Fin m => if (j : ℕ) < (l : ℕ) + 1 then ‖x j‖ ^ 2 else 0)
    (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ l)
  have h2 : (if (l : ℕ) < (l : ℕ) + 1 then ‖x l‖ ^ 2 else 0) = ‖x l‖ ^ 2 :=
    ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self _) h
  simp only [h2] at h
  linarith

theorem partialSq_smul_le {s : ℂ} (hs : ‖s‖ ≤ 1) (x : Fin m → ℂ) (l : ℕ) :
    partialSq (s • x) l ≤ partialSq x l := by
  unfold partialSq
  have hs2 : ‖s‖ ^ 2 ≤ 1 := by
    have := norm_nonneg s
    nlinarith
  have h : (∑ j : Fin m, if (j : ℕ) < l then ‖(s • x) j‖ ^ 2 else 0) ≤
      ∑ j : Fin m, if (j : ℕ) < l then ‖x j‖ ^ 2 else 0 := by
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
      nlinarith [sq_nonneg ‖x j‖]
    · exact le_rfl
  linarith

/-! ## Gram determinants of the chart matrices -/

/-- The entries of `x` at positions `≥ l`. -/
def tailVec (l : ℕ) (x : Fin m → ℂ) : Fin m → ℂ := fun j => if l ≤ (j : ℕ) then x j else 0

theorem Jmat_castSucc (r : Fin (m + 1) → ℂ) (i : Fin m) :
    Jmat r i.castSucc = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i.castSucc := by
  funext j
  simp [Jmat]

theorem Jmat_last (r : Fin (m + 1) → ℂ) : Jmat r (Fin.last m) = r := by
  funext j
  simp [Jmat]

theorem sum_one_mul (a : Fin (m + 1)) (f : Fin (m + 1) → ℂ) :
    ∑ j, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) a j * f j = f a := by
  simp [Matrix.one_apply]

theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem paddedGram_chart {l : ℕ} (hl : l ≤ m) (x : Fin m → ℂ) :
    ComplexGramFormula.paddedGram l (Jmat (Fin.snoc x 1 : Fin (m + 1) → ℂ))
        (Jmat (Fin.snoc (star x) 1 : Fin (m + 1) → ℂ)) =
      Jmat (Fin.snoc (tailVec l x) 1 : Fin (m + 1) → ℂ) *
        (Jmat (Fin.snoc (tailVec l (star x)) ((partialSq x l : ℝ) : ℂ) :
          Fin (m + 1) → ℂ))ᵀ := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [ComplexGramFormula.paddedGram, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  refine Fin.lastCases ?_ (fun p' => ?_) p <;> refine Fin.lastCases ?_ (fun q' => ?_) q
  · rw [ite_eq_left (by simp [hl])]
    simp only [Jmat_last]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    unfold partialSq tailVec
    have h : ∀ j : Fin m, x j * (star x) j = (if l ≤ (j : ℕ) then x j else 0) *
        (if l ≤ (j : ℕ) then (star x) j else 0) +
          (((if (j : ℕ) < l then ‖x j‖ ^ 2 else 0 : ℝ)) : ℂ) := by
      intro j
      by_cases hj : l ≤ (j : ℕ)
      · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_right (by omega)]
        simp
      · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_left (by omega), Pi.star_apply,
          mul_star_eq]
        simp
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib]
    push_cast
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

theorem gram_chart {l : ℕ} (hl : l ≤ m) (x : Fin m → ℂ) :
    ComplexGramFormula.gram l (Jmat (Fin.snoc x 1 : Fin (m + 1) → ℂ))
        (Jmat (Fin.snoc (star x) 1 : Fin (m + 1) → ℂ)) = ((partialSq x l : ℝ) : ℂ) := by
  rw [ComplexGramFormula.gram, paddedGram_chart hl, Matrix.det_mul, Matrix.det_transpose,
    det_Jmat, det_Jmat]
  simp

theorem Jmat_map_conj (r : Fin (m + 1) → ℂ) : (Jmat r).map (starRingEnd ℂ) = Jmat (star r) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [Jmat]
  · simp only [Matrix.map_apply, Jmat, Matrix.of_apply, Fin.lastCases_castSucc, Matrix.one_apply]
    split_ifs <;> simp

theorem star_snoc_one (x : Fin m → ℂ) :
    star (Fin.snoc x 1 : Fin (m + 1) → ℂ) = (Fin.snoc (star x) 1 : Fin (m + 1) → ℂ) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

theorem paddedGram_mul_unitary {n : ℕ} (y z κ : Matrix (Fin n) (Fin n) ℂ)
    (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1) (l : ℕ) :
    ComplexGramFormula.paddedGram l (y * κ) (z * κ.map (starRingEnd ℂ)) =
      ComplexGramFormula.paddedGram l y z := by
  ext p q
  simp only [ComplexGramFormula.paddedGram, Matrix.of_apply]
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κ, hκ, Matrix.one_mul]

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

variable {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ} {c : (Fin (m + 1) → ℂˣ) → ℂ} {σ : ℕ → ℝ}

theorem prod_tail_sq_eq (x : Fin m → ℂ) (κ : Langlands.GeneralLinear (m + 1) ℂ)
    (hκ : κ ∈ unitaryCompact ℂ (m + 1)) (a : Fin (m + 1) → ℂˣ) (u : upperUnipotent (m + 1) ℂ)
    (k : Langlands.GeneralLinear (m + 1) ℂ) (hk : k ∈ unitaryCompact ℂ (m + 1))
    (hg : chartGL x * κ = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℂ) *
      (u : Langlands.GeneralLinear (m + 1) ℂ) * k) {l : ℕ} (hl : l ≤ m) :
    ‖∏ j : Fin (m + 1), if l ≤ (j : ℕ) then (a j : ℂ) else 1‖ ^ 2 = partialSq x l := by
  have hκ' := ComplexGramFormula.mul_conj_transpose_eq_one_of_mem hκ
  have hk' := ComplexGramFormula.mul_conj_transpose_eq_one_of_mem hk
  have hval := congrArg (fun g : Langlands.GeneralLinear (m + 1) ℂ =>
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) hg
  simp only [Units.val_mul, Iwasawa.diagonalUnits_val] at hval
  have h1 := congrArg (fun y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ =>
    ComplexGramFormula.gram l y (y.map (starRingEnd ℂ))) hval
  have hlhs : ComplexGramFormula.gram l
      ((chartGL x : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * (κ : Matrix _ _ ℂ))
      (((chartGL x : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * (κ : Matrix _ _ ℂ)).map
        (starRingEnd ℂ)) = ((partialSq x l : ℝ) : ℂ) := by
    rw [Matrix.map_mul, ComplexGramFormula.gram, paddedGram_mul_unitary _ _ _ hκ',
      ← ComplexGramFormula.gram, chartGL, JGL_val, Jmat_map_conj, star_snoc_one, gram_chart hl]
  have hrhs : ComplexGramFormula.gram l
      (Matrix.diagonal (fun i => (a i : ℂ)) * ((u : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * (k : Matrix _ _ ℂ))
      ((Matrix.diagonal (fun i => (a i : ℂ)) * ((u : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * (k : Matrix _ _ ℂ)).map (starRingEnd ℂ)) =
      ((‖∏ j : Fin (m + 1), if l ≤ (j : ℕ) then (a j : ℂ) else 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [ComplexGramFormula.gram_mul_conj (ComplexGramFormula.isUpperTriangular_diagonal_mul a u)
      hk']
    congr 3
    rw [GramFormula.diagonalTail]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ComplexGramFormula.diagonal_mul_apply_self]
  rw [hlhs, hrhs] at h1
  exact_mod_cast h1.symm

/-- **Growth along the chart.** If `F(diag(a) u g) = c(a) F(g)` with `‖c(a)‖ = ∏ |a_l|^{σ_l}`
and `‖F‖ ≤ C` on `U(m+1)`, then
`‖F(J(x,1) κ)‖ ≤ C ∏_{l<m} r_{l+1}(x)^{(σ_{l+1} - σ_l)/2}` for `κ ∈ U(m+1)`. -/
theorem norm_le_chart
    (hF : ∀ (a : Fin (m + 1) → ℂˣ) (u : upperUnipotent (m + 1) ℂ)
      (g : Langlands.GeneralLinear (m + 1) ℂ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℂ) *
        (u : Langlands.GeneralLinear (m + 1) ℂ) * g) = c a * F g)
    (hc : ∀ a, ‖c a‖ = ∏ l : Fin (m + 1), ‖(a l : ℂ)‖ ^ σ l)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℂ (m + 1), ‖F k‖ ≤ C)
    (x : Fin m → ℂ) {κ : Langlands.GeneralLinear (m + 1) ℂ}
    (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    ‖F (chartGL x * κ)‖ ≤
      C * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ ((σ ((l : ℕ) + 1) - σ l) / 2) := by
  obtain ⟨a, u, k, hk, hg⟩ :=
    ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary (chartGL x * κ)
  rw [hg, hF, norm_mul, hc, mul_comm]
  have hprod : ∏ l : Fin (m + 1), ‖(a l : ℂ)‖ ^ σ l =
      ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ ((σ ((l : ℕ) + 1) - σ l) / 2) := by
    have ha : ∀ l, 0 < ‖(a l : ℂ)‖ := fun l => norm_pos_iff.mpr (a l).ne_zero
    set T : ℕ → ℝ := fun l => ∑ j : Fin (m + 1),
      if l ≤ (j : ℕ) then Real.log ‖(a j : ℂ)‖ else 0 with hTdef
    have hT : ∀ l : ℕ, l ≤ m → T l = Real.log (partialSq x l) / 2 := by
      intro l hl
      have h := prod_tail_sq_eq x κ hκ a u k hk hg hl
      rw [← h, Real.log_pow, norm_prod, Real.log_prod]
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
    have hsum := sum_mul_eq_sum_sub (t := fun l => Real.log ‖(a l : ℂ)‖) (σ := σ) (T := T)
      (fun l => rfl) hT0
    rw [← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (ha l) _),
      ← Real.exp_log (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (partialSq_pos x _) _),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (ha l) _).ne'),
      Real.log_prod (fun l _ => (Real.rpow_pos_of_pos (partialSq_pos x _) _).ne')]
    congr 1
    simp only [Real.log_rpow (ha _), Real.log_rpow (partialSq_pos x _)]
    rw [show (∑ l : Fin (m + 1), σ l * Real.log ‖(a l : ℂ)‖) = _ from hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hT _ (by have := l.isLt; omega)]
    ring
  rw [hprod]
  exact mul_le_mul_of_nonneg_right (hC k hk)
    (Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (partialSq_pos x _) _).le)

end Bound

/-! ## Integrability of the dominating function -/

theorem integrable_one_add_sq_rpow {γ : ℝ} (hγ : γ < -1) :
    Integrable fun t : ℂ => (1 + ‖t‖ ^ 2) ^ γ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := -2 * γ)
    (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only
  congr 1
  ring

theorem integrable_prod_one_add_sq_rpow {γ : Fin m → ℝ} (hγ : ∀ l, γ l < -1) :
    Integrable fun x : Fin m → ℂ => ∏ l, (1 + ‖x l‖ ^ 2) ^ γ l := by
  have h := Integrable.fintype_prod (f := fun l (t : ℂ) => (1 + ‖t‖ ^ 2) ^ γ l)
    (μ := fun _ => (volume : Measure ℂ)) fun l => integrable_one_add_sq_rpow (hγ l)
  rwa [← volume_pi] at h

/-! ## Domination -/

theorem prod_partialSq_rpow_le {x : Fin m → ℂ} {ε : Fin m → ℝ} (hε : ∀ l, ε l ≤ 0) :
    ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ ε l ≤ ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ ε l :=
  Finset.prod_le_prod₀ (fun l _ => (Real.rpow_pos_of_pos (partialSq_pos x _) _).le)
    fun l _ => Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_sq_le_partialSq x l) (hε l)

/-- The product of the bounds for a pair of dual functions, the first one evaluated at the
contracted point `s • x` with `|s| ≤ 1`, is dominated by `∏ (1 + |x_l|²)^{max(ε^h_l, -2)}`. -/
theorem prod_rpow_mul_prod_rpow_le {x : Fin m → ℂ} {s : ℂ} (hs : ‖s‖ ≤ 1) {εu εh : Fin m → ℝ}
    (hsum : ∀ l, εu l + εh l = -2) (hneg : ∀ l, εh l < 0) :
    (∏ l : Fin m, partialSq (s • x) ((l : ℕ) + 1) ^ εu l) *
        ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ εh l ≤
      ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ max (εh l) (-2) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun l _ => mul_nonneg
    (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le
    (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le) fun l _ => ?_
  set A := partialSq (s • x) ((l : ℕ) + 1)
  set B := partialSq x ((l : ℕ) + 1)
  have hA : 1 ≤ A := one_le_partialSq _ _
  have hB : 1 ≤ B := one_le_partialSq _ _
  have hAB : A ≤ B := partialSq_smul_le hs x _
  have hmax : max (εh l) (-2) ≤ 0 := max_le (hneg l).le (by norm_num)
  have h1 : A ^ εu l * B ^ εh l ≤ B ^ max (εh l) (-2) := by
    by_cases hu : 0 ≤ εu l
    · calc A ^ εu l * B ^ εh l ≤ B ^ εu l * B ^ εh l :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hAB hu)
              (Real.rpow_pos_of_pos (by linarith) _).le
        _ = B ^ (-2 : ℝ) := by rw [← Real.rpow_add (by linarith), hsum l]
        _ ≤ B ^ max (εh l) (-2) := Real.rpow_le_rpow_of_exponent_le hB (le_max_right _ _)
    · calc A ^ εu l * B ^ εh l ≤ 1 * B ^ εh l :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith))
              (Real.rpow_pos_of_pos (by linarith) _).le
        _ = B ^ εh l := one_mul _
        _ ≤ B ^ max (εh l) (-2) := Real.rpow_le_rpow_of_exponent_le hB (le_max_left _ _)
  exact h1.trans (Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_sq_le_partialSq x l) hmax)

end ComplexParabolicChartBound

open ComplexParabolicChartBound ComplexMaximalParabolicIntegration Langlands.GeneralLinear

/-- **Statement (growth along the opposite unipotent radical of `P_{m,1}` of `GL_{m+1}(ℂ)`).** Let
`F : GL_{m+1}(ℂ) → ℂ` satisfy `F(diag(a) u g) = c(a) F(g)` for all `a ∈ (ℂˣ)^{m+1}`, upper
unipotent `u` and `g`, where `‖c(a)‖ = ∏_l |a_l|^{σ_l}`, and let `‖F‖ ≤ C` on `U(m+1)`. Then for
every `x ∈ ℂ^m` and `κ ∈ U(m+1)`,
`‖F(J(x,1) κ)‖ ≤ C ∏_{l<m} (1 + ∑_{j ≤ l} |x_j|²)^{(σ_{l+1} - σ_l)/2}`,
where `J(x,1)` is the identity matrix with last row `(x, 1)` (`chartGL x`). -/
def ComplexParabolicChartBoundStatement : Prop :=
  ∀ (m : ℕ) (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (c : (Fin (m + 1) → ℂˣ) → ℂ)
    (σ : ℕ → ℝ),
    (∀ (a : Fin (m + 1) → ℂˣ) (u : upperUnipotent (m + 1) ℂ)
      (g : Langlands.GeneralLinear (m + 1) ℂ),
      F ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℂ) *
        (u : Langlands.GeneralLinear (m + 1) ℂ) * g) = c a * F g) →
    (∀ a, ‖c a‖ = ∏ l : Fin (m + 1), ‖(a l : ℂ)‖ ^ σ l) →
    ∀ C : ℝ, (∀ k ∈ unitaryCompact ℂ (m + 1), ‖F k‖ ≤ C) →
      ∀ (x : Fin m → ℂ) (κ : Langlands.GeneralLinear (m + 1) ℂ), κ ∈ unitaryCompact ℂ (m + 1) →
        ‖F (chartGL x * κ)‖ ≤
          C * ∏ l : Fin m, (1 + ∑ j : Fin m, if (j : ℕ) < (l : ℕ) + 1 then ‖x j‖ ^ 2 else 0) ^
            ((σ ((l : ℕ) + 1) - σ l) / 2)

theorem complexParabolicChartBound : ComplexParabolicChartBoundStatement :=
  fun _ _ _ _ hF hc _ hC _ _ hκ => norm_le_chart hF hc hC _ hκ

end Langlands.Archimedean
