import Langlands.Global.RankinSelberg.RectangularJointCoordinates

/-! # Full idelic norms on a fixed finite denominator -/

noncomputable section
universe u
open NumberField
open scoped Classical NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

/-- The mixed archimedean supremum norm of the value of an idele. -/
def ideleArchimedeanNorm (z : Ideles F) : ℝ :=
  ‖archimedeanAdeleProjection F (z : Adeles F)‖

/-- The mixed-space norm bounds each archimedean completion norm. -/
theorem infiniteProjection_norm_le_mixed (x : Adeles F) (v : InfinitePlace F) :
    ‖infiniteProjection F v x‖ ≤ ‖archimedeanAdeleProjection F x‖ := by
  change ‖x.1 v‖ ≤ _
  rcases v.isReal_or_isComplex with hv | hv
  · rw [← PrimitiveAdelicHeight.norm_realCoord x.1 ⟨v, hv⟩]
    exact (norm_le_pi_norm (archimedeanAdeleProjection F x).1 ⟨v, hv⟩).trans
      (norm_fst_le _)
  · rw [← PrimitiveAdelicHeight.norm_complexCoord x.1 ⟨v, hv⟩]
    exact (norm_le_pi_norm (archimedeanAdeleProjection F x).2 ⟨v, hv⟩).trans
      (norm_snd_le _)

/-- An integral finite value contributes a factor at most one to the
full idelic absolute value. -/
theorem full_idele_norm_le_archimedean_power
    (z : Ideles F) (hz : (z : Adeles F).2 ∈ integralFiniteAdeles F) :
    ((IdeleAbsoluteValue.full F z : ℝ≥0) : ℝ) ≤
      ideleArchimedeanNorm F z ^ Module.finrank ℚ F := by
  have hfin (v : FinitePlace F) : ‖(z : Adeles F).2 v‖ ≤ 1 := by
    have hh := (mem_integralFiniteAdeles F _).mp hz v
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using hh
  have hs : (fun v : FinitePlace F => ‖(z : Adeles F).2 v‖).HasFiniteMulSupport :=
    NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (ideleProductEquiv F z).2
  have hf : ∏ᶠ v : FinitePlace F, ‖(z : Adeles F).2 v‖ ≤ 1 := by
    have hh := finprod_le_finprod₀ hs (fun _ => norm_nonneg _)
      (show (fun _ : FinitePlace F => (1 : ℝ)).HasFiniteMulSupport from
        Function.hasFiniteMulSupport_one) hfin
    simpa using hh
  have hi :
      (∏ v : InfinitePlace F, ‖(z : Adeles F).1 v‖ ^ v.mult) ≤
        ideleArchimedeanNorm F z ^ Module.finrank ℚ F := by
    calc
      _ ≤ ∏ v : InfinitePlace F, ideleArchimedeanNorm F z ^ v.mult :=
        Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _)
          (fun v _ => pow_le_pow_left₀ (norm_nonneg _)
            (infiniteProjection_norm_le_mixed F (z : Adeles F) v) _)
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  rw [IdeleAbsoluteValue.coe_full]
  exact (mul_le_mul_of_nonneg_left hf
    (Finset.prod_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _))).trans
      (by simpa using hi)

/-- A common nonzero field denominator turns the full idelic absolute
value into a fixed archimedean polynomial bound. -/
theorem full_idele_norm_le_of_denominator
    (z : Ideles F) (q : F) (hq : q ≠ 0)
    (hz : algebraMap F (FiniteAdeles F) q * (z : Adeles F).2 ∈ integralFiniteAdeles F) :
    ((IdeleAbsoluteValue.full F z : ℝ≥0) : ℝ) ≤
      ‖archimedeanAdeleProjection F (diagonal F q)‖ ^ Module.finrank ℚ F *
        ideleArchimedeanNorm F z ^ Module.finrank ℚ F := by
  let delta := diagonalUnits F (Units.mk0 q hq)
  let w : Ideles F := delta * z
  have hd : (delta : Adeles F) = diagonal F q := rfl
  have hw : (w : Adeles F).2 ∈ integralFiniteAdeles F := by
    change ((delta : Adeles F) * (z : Adeles F)).2 ∈ integralFiniteAdeles F
    rw [hd]
    exact hz
  have habs : IdeleAbsoluteValue.full F w = IdeleAbsoluteValue.full F z := by
    dsimp only [w, delta]
    rw [map_mul, IdeleAbsoluteValue.full_diagonalUnits, one_mul]
  have hnorm :
      ideleArchimedeanNorm F w ≤
        ‖archimedeanAdeleProjection F (diagonal F q)‖ * ideleArchimedeanNorm F z := by
    unfold ideleArchimedeanNorm
    change ‖archimedeanAdeleProjection F ((delta : Adeles F) * (z : Adeles F))‖ ≤ _
    rw [map_mul, hd]
    exact norm_mul_le _ _
  have hh := full_idele_norm_le_archimedean_power F w hw
  rw [habs] at hh
  apply hh.trans
  calc
    _ ≤ (‖archimedeanAdeleProjection F (diagonal F q)‖ * ideleArchimedeanNorm F z) ^
        Module.finrank ℚ F :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ = _ := mul_pow _ _ _

/-- An idele integral at finite places and bounded by one at all mixed
archimedean coordinates has full absolute value at most one. -/
theorem full_idele_norm_le_one
    (z : Ideles F) (hz : (z : Adeles F).2 ∈ integralFiniteAdeles F)
    (harch : ideleArchimedeanNorm F z ≤ 1) :
    ((IdeleAbsoluteValue.full F z : ℝ≥0) : ℝ) ≤ 1 :=
  (full_idele_norm_le_archimedean_power F z hz).trans
    (pow_le_one₀ (norm_nonneg _) harch)

end Langlands.Global.RankinSelbergGlobal
