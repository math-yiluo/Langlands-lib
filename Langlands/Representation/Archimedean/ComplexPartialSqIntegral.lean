import Langlands.Representation.Archimedean.ComplexParabolicChartBound

/-!
# Integrability of products of partial square sums on `ℂ^m`

For `r_l(x) = 1 + ∑_{j<l} |x_j|²` (`ComplexParabolicChartBound.partialSq`) and real exponents
`γ_0, …, γ_{m-1}`, the function `x ↦ ∏_l r_{l+1}(x)^{γ_l}` is integrable on `ℂ^m` as soon as
`∑_{l ≥ j} (γ_l + 1) < 0` for every `j` (`ComplexPartialSqIntegral.integrable_prod_partialSq`).
This allows exponents `γ_l = -1` (ties of the Langlands order) as long as every tail sum of
`γ_l + 1` is negative.
-/

noncomputable section

open MeasureTheory

namespace Langlands.Archimedean

set_option autoImplicit false

namespace ComplexPartialSqIntegral

open ComplexParabolicChartBound

/-! ## One complex variable -/

theorem integral_add_sq_rpow {A : ℝ} (hA : 0 < A) (β : ℝ) :
    ∫ t : ℂ, (A + ‖t‖ ^ 2) ^ β = A ^ (β + 1) * ∫ t : ℂ, (1 + ‖t‖ ^ 2) ^ β := by
  have hs : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ))
    (fun t : ℂ => (A + ‖t‖ ^ 2) ^ β) (Real.sqrt A)
  have hpt : ∀ t : ℂ, (A + ‖Real.sqrt A • t‖ ^ 2) ^ β = A ^ β * (1 + ‖t‖ ^ 2) ^ β := by
    intro t
    rw [norm_smul, Real.norm_of_nonneg hs, mul_pow, Real.sq_sqrt hA.le,
      show A + A * ‖t‖ ^ 2 = A * (1 + ‖t‖ ^ 2) by ring,
      Real.mul_rpow hA.le (by positivity)]
  simp only [hpt, integral_const_mul, Complex.finrank_real_complex, Real.sq_sqrt hA.le,
    smul_eq_mul] at h
  rw [abs_of_pos (inv_pos.mpr hA)] at h
  rw [Real.rpow_add_one hA.ne']
  field_simp at h
  linarith

theorem integrable_add_sq_rpow {A : ℝ} (hA : 0 < A) {β : ℝ} (hβ : β < -1) :
    Integrable fun t : ℂ => (A + ‖t‖ ^ 2) ^ β := by
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have h := ((integrable_one_add_sq_rpow hβ).comp_smul (inv_ne_zero hs.ne')).const_mul (A ^ β)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), mul_pow, inv_pow,
    Real.sq_sqrt hA.le, ← Real.mul_rpow hA.le (by positivity)]
  congr 1
  field_simp

/-! ## Partial square sums of `Fin.snoc` -/

theorem partialSq_snoc_castSucc {m : ℕ} (y : Fin m → ℂ) (t : ℂ) (l : Fin m) :
    partialSq (Fin.snoc y t : Fin (m + 1) → ℂ) ((l : ℕ) + 1) = partialSq y ((l : ℕ) + 1) := by
  unfold partialSq
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have : ¬ (m < (l : ℕ) + 1) := by omega
  simp [this]

theorem partialSq_snoc_last {m : ℕ} (y : Fin m → ℂ) (t : ℂ) :
    partialSq (Fin.snoc y t : Fin (m + 1) → ℂ) (m + 1) = partialSq y m + ‖t‖ ^ 2 := by
  unfold partialSq
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin m, (j : ℕ) < m + 1 := fun j => by omega
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, lt_add_one,
    ite_true, h1, Fin.is_lt]
  ring

theorem continuous_partialSq {m : ℕ} (l : ℕ) : Continuous fun x : Fin m → ℂ => partialSq x l := by
  unfold partialSq
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  split_ifs
  · exact ((continuous_apply j).norm).pow 2
  · exact continuous_const

/-! ## The integrability criterion -/

/-- The tail condition `δ + ∑_{l ≥ j} (γ_l + 1) < 0` for every `j`. -/
def TailCondition {m : ℕ} (γ : Fin m → ℝ) (δ : ℝ) : Prop :=
  ∀ j : Fin m, δ + ∑ l : Fin m, (if j ≤ l then γ l + 1 else 0) < 0

theorem integrable_partialSq_mul_prod : ∀ (m : ℕ) (γ : Fin m → ℝ) (δ : ℝ), TailCondition γ δ →
    Integrable fun y : Fin m → ℂ =>
      partialSq y m ^ δ * ∏ l : Fin m, partialSq y ((l : ℕ) + 1) ^ γ l
  | 0, γ, δ, _ => by
      have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) :=
        ⟨by rw [volume_pi, Measure.pi_univ]; simp⟩
      simp only [partialSq_zero, Real.one_rpow, Finset.univ_eq_empty, Finset.prod_empty,
        mul_one]
      exact integrable_const _
  | m + 1, γ, δ, hγ => by
      set β : ℝ := δ + γ (Fin.last m) with hβdef
      have hβ : β < -1 := by
        have := hγ (Fin.last m)
        have hsum : (∑ l : Fin (m + 1), (if Fin.last m ≤ l then γ l + 1 else 0)) =
            γ (Fin.last m) + 1 := by
          rw [Fin.sum_univ_castSucc]
          simp
        rw [hsum] at this
        linarith
      set γ' : Fin m → ℝ := fun l => γ (Fin.castSucc l) with hγ'def
      have hIH := integrable_partialSq_mul_prod m γ' (β + 1) (fun j => by
        have := hγ (Fin.castSucc j)
        rw [Fin.sum_univ_castSucc] at this
        simp only [Fin.castSucc_le_castSucc_iff, Fin.le_last, ite_true] at this
        simp only [hγ'def]
        linarith)
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)
      have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)
      set G : ℂ × (Fin m → ℂ) → ℝ := fun p =>
        (partialSq p.2 m + ‖p.1‖ ^ 2) ^ β * ∏ l : Fin m, partialSq p.2 ((l : ℕ) + 1) ^ γ' l
        with hGdef
      have key : (fun x : Fin (m + 1) → ℂ =>
          partialSq x (m + 1) ^ δ * ∏ l : Fin (m + 1), partialSq x ((l : ℕ) + 1) ^ γ l) ∘
            e.symm = G := by
        funext p
        obtain ⟨t, y⟩ := p
        simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply, hGdef]
        have hx : (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℂ) (Fin.last m)) (t, y) =
            (Fin.snoc y t : Fin (m + 1) → ℂ) := Fin.insertNth_last' _ _
        rw [hx, Fin.prod_univ_castSucc]
        simp only [partialSq_snoc_castSucc, Fin.val_castSucc, Fin.val_last]
        rw [partialSq_snoc_last]
        have hpos : 0 < partialSq y m + ‖t‖ ^ 2 := by
          have := partialSq_pos y m
          positivity
        rw [hβdef, Real.rpow_add hpos]
        simp only [hγ'def]
        ring
      refine (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mp ?_
      rw [key]
      have hGc : Continuous G := by
        refine Continuous.mul ?_ (continuous_finsetProd _ fun l _ => ?_)
        · refine Continuous.rpow_const (((continuous_partialSq m).comp continuous_snd).add
            (continuous_fst.norm.pow 2)) fun p => Or.inl ?_
          have := partialSq_pos p.2 m
          positivity
        · exact ((continuous_partialSq _).comp continuous_snd).rpow_const fun p =>
            Or.inl (partialSq_pos p.2 _).ne'
      rw [Measure.volume_eq_prod, integrable_prod_iff' hGc.aestronglyMeasurable]
      refine ⟨ae_of_all _ fun y => ?_, ?_⟩
      · simp only [hGdef]
        exact (integrable_add_sq_rpow (partialSq_pos y m) hβ).mul_const _
      · have heq : (fun y : Fin m → ℂ => ∫ t : ℂ, ‖G (t, y)‖) = fun y =>
            (∫ t : ℂ, (1 + ‖t‖ ^ 2) ^ β) *
              (partialSq y m ^ (β + 1) * ∏ l : Fin m, partialSq y ((l : ℕ) + 1) ^ γ' l) := by
          funext y
          have hnn : ∀ t : ℂ, ‖(partialSq y m + ‖t‖ ^ 2) ^ β *
              ∏ l : Fin m, partialSq y ((l : ℕ) + 1) ^ γ' l‖ =
              (partialSq y m + ‖t‖ ^ 2) ^ β * ∏ l : Fin m, partialSq y ((l : ℕ) + 1) ^ γ' l :=
            fun t => by
              refine Real.norm_of_nonneg (mul_nonneg ?_ (Finset.prod_nonneg fun l _ =>
                (Real.rpow_pos_of_pos (partialSq_pos y _) _).le))
              exact (Real.rpow_pos_of_pos (by
                have := partialSq_pos y m
                positivity) _).le
          simp only [hGdef, hnn]
          rw [integral_mul_const, integral_add_sq_rpow (partialSq_pos y m)]
          ring
        rw [heq]
        exact hIH.const_mul _

/-- **Integrability of products of partial square sums.** -/
theorem integrable_prod_partialSq {m : ℕ} {γ : Fin m → ℝ} (hγ : TailCondition γ 0) :
    Integrable fun x : Fin m → ℂ => ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ γ l := by
  have h := integrable_partialSq_mul_prod m γ 0 hγ
  simpa only [Real.rpow_zero, one_mul] using h

/-- The tail condition holds when every `γ_l ≤ -1` and the last exponent is `< -1`. -/
theorem tailCondition_of_le {m : ℕ} {γ : Fin (m + 1) → ℝ} (hle : ∀ l, γ l ≤ -1)
    (hlast : γ (Fin.last m) < -1) : TailCondition γ 0 := by
  intro j
  rw [zero_add, Fin.sum_univ_castSucc]
  have h1 : ∑ l : Fin m, (if j ≤ Fin.castSucc l then γ (Fin.castSucc l) + 1 else 0) ≤ 0 :=
    Finset.sum_nonpos fun l _ => by
      split_ifs
      · linarith [hle (Fin.castSucc l)]
      · exact le_rfl
  have h2 : (if j ≤ Fin.last m then γ (Fin.last m) + 1 else 0) = γ (Fin.last m) + 1 :=
    by simp [Fin.le_last j]
  rw [h2]
  linarith

end ComplexPartialSqIntegral

/-- **Statement (integrability of products of partial square sums on `ℂ^m`).** For real
exponents `γ_0, …, γ_{m-1}` with `∑_{l ≥ j} (γ_l + 1) < 0` for every `j`, the function
`x ↦ ∏_l (1 + ∑_{i ≤ l} |x_i|²)^{γ_l}` is integrable on `ℂ^m`. -/
def ComplexPartialSqIntegrableStatement : Prop :=
  ∀ (m : ℕ) (γ : Fin m → ℝ),
    (∀ j : Fin m, ∑ l : Fin m, (if j ≤ l then γ l + 1 else 0) < 0) →
    MeasureTheory.Integrable fun x : Fin m → ℂ =>
      ∏ l : Fin m, ComplexParabolicChartBound.partialSq x ((l : ℕ) + 1) ^ γ l

theorem complexPartialSqIntegrable : ComplexPartialSqIntegrableStatement := by
  intro m γ hγ
  exact ComplexPartialSqIntegral.integrable_prod_partialSq (fun j => by simpa using hγ j)

end Langlands.Archimedean
