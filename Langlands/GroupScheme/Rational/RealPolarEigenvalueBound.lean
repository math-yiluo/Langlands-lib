import Langlands.GroupScheme.Rational.RealAdditiveFactorGrowth
import Langlands.GroupScheme.Rational.PositivePowerFactorizationProof
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Eigenvalue bounds from a bounded torus factor and a polynomial additive factor -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.RealPolar

variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Entrywise bound for `(A * B) *ᵥ v`. -/
theorem abs_mul_mulVec_le (A B : Matrix n n ℝ) (v : n → ℝ) {α β : ℝ}
    (hA : ∀ j l, |A j l| ≤ α) (hB : ∀ l k, |B l k| ≤ β) (j : n) :
    |((A * B) *ᵥ v) j| ≤ α * (Fintype.card n * (β * ∑ k, |v k|)) := by
  have hα : 0 ≤ α := (abs_nonneg _).trans (hA j j)
  have hβ : 0 ≤ β := by
    by_cases h : Nonempty n
    · obtain ⟨l⟩ := h
      exact (abs_nonneg _).trans (hB l l)
    · simp only [not_nonempty_iff] at h
      exact (isEmpty_iff.mp h j).elim
  have hw : ∀ l, |(B *ᵥ v) l| ≤ β * ∑ k, |v k| := by
    intro l
    simp only [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hB l k) (abs_nonneg _)
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |A j l * (B *ᵥ v) l| ≤ ∑ _l : n, α * (β * ∑ k, |v k|) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hA j l) (hw l) (abs_nonneg _) hα
    _ = α * (Fintype.card n * (β * ∑ k, |v k|)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- An exponential with base greater than one eventually beats every polynomial bound. -/
theorem le_one_of_pow_le_poly {r K a : ℝ} {D : ℕ} (ha : 0 < a)
    (h : ∀ N : ℕ, r ^ N * a ≤ K * ((N : ℝ) + 1) ^ D) (hr : 0 ≤ r) : r ≤ 1 := by
  by_contra hr1
  rw [not_le] at hr1
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt D hr1).comp (tendsto_add_atTop_nat 1)
  have hK : 0 < K := by
    have := h 0
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, one_pow, mul_one] at this
    linarith
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < a / (K * r) by positivity))
  obtain ⟨N, hN⟩ := hev.exists
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hN
  have hpos : 0 < r ^ (N + 1) := by positivity
  rw [div_lt_div_iff₀ hpos (by positivity)] at hN
  have := h N
  rw [pow_succ] at hN
  nlinarith [mul_pos hK (show 0 < r ^ N by positivity)]

/-- Let the torus factors of positive-power factorizations have bounded matrices. If the matrix
of a real point has an eigenvector with nonnegative eigenvalue `ev`, then `ev ≤ 1`. -/
theorem eigenvalue_le_one {G : GroupScheme (Spec (CommRingCat.of ℝ))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (ρ : MatrixRepresentation G n)
    (hbound : ∀ (T : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : T.toGrp ⟶ G),
      IsTorus T.toGrp → IsClosedSubgroup i → ∃ α : ℝ, ∀ (s : rationalPoints T.toGrp) (j l : n),
        |(ρ.rationalMatrix (rationalPoints.map i s) : Matrix n n ℝ) j l| ≤ α)
    (x : rationalPoints G) {ev : ℝ} (hev : 0 ≤ ev) {v : n → ℝ} (hv : v ≠ 0)
    (hxv : (ρ.rationalMatrix x : Matrix n n ℝ) *ᵥ v = ev • v) : ev ≤ 1 := by
  obtain ⟨m, hm, T, i, t, φ, hT, hi, hx, hcomm⟩ :=
    positivePowerTorusAdditiveFactorization_commute ℝ G x
  obtain ⟨α, hα⟩ := hbound T i hT hi
  choose d c hc hdc using fun p : n × n =>
    RealAdditiveFactor.exists_rationalMatrix_entry_bound ρ φ p.1 p.2
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  have hpow : ∀ N : ℕ, x ^ (m * N) = rationalPoints.map i (t ^ N) *
      rationalPoints.map φ (VectorGroup.coordinateOnePoint ℝ ^ N) := by
    intro N
    rw [pow_mul, hx, hcomm.mul_pow, map_pow, map_pow]
  have heig : ∀ k : ℕ, (ρ.rationalMatrix x : Matrix n n ℝ) ^ k *ᵥ v = ev ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hxv, smul_smul, pow_succ]
  have hB : ∀ (N : ℕ) (l k : n), |(ρ.rationalMatrix (rationalPoints.map φ
      (VectorGroup.coordinateOnePoint ℝ ^ N)) : Matrix n n ℝ) l k| ≤
        (∑ p, c p) * ((N : ℝ) + 1) ^ (∑ p, d p) := by
    intro N l k
    refine (hdc (l, k) N).trans ?_
    have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
    exact mul_le_mul
      (Finset.single_le_sum (fun p _ => (hc p).le) (Finset.mem_univ (l, k)))
      (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun p _ => Nat.zero_le (d p))
        (Finset.mem_univ (l, k))))
      (by positivity) (Finset.sum_nonneg fun p _ => (hc p).le)
  have hmain : ∀ N : ℕ, (ev ^ m) ^ N * |v j| ≤
      (α * (Fintype.card n * ((∑ p, c p) * ∑ k, |v k|))) * ((N : ℝ) + 1) ^ (∑ p, d p) := by
    intro N
    have h := abs_mul_mulVec_le _ _ v (hα (t ^ N)) (hB N) j
    have hval : (ρ.rationalMatrix (rationalPoints.map i (t ^ N)) : Matrix n n ℝ) *
        (ρ.rationalMatrix (rationalPoints.map φ (VectorGroup.coordinateOnePoint ℝ ^ N)) :
          Matrix n n ℝ) = (ρ.rationalMatrix x : Matrix n n ℝ) ^ (m * N) := by
      rw [← Units.val_mul, ← map_mul, ← hpow, map_pow, Units.val_pow_eq_pow_val]
    rw [hval, heig, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg hev _),
      pow_mul] at h
    calc (ev ^ m) ^ N * |v j| ≤ _ := h
      _ = _ := by ring
  have := le_one_of_pow_le_poly (abs_pos.mpr hj) hmain (pow_nonneg hev m)
  exact (pow_le_one_iff_of_nonneg hev hm.ne').mp this

end Langlands.GroupScheme.RealPolar
