import Langlands.Representation.RankinSelberg.OneVariableMellinProof

/-! Actual scalar Mellin data retaining a common convergence half-plane. -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF

section Definitions

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- Scalar multiplicative-Haar Mellin integrand with positive integral weight. -/
def scalarMellinIntegrand (abv : F → ℝ) (η : Fˣ → ℂ) (m : ℕ)
    (Φ : SchwartzBruhat F) (s : ℂ) (a : Fˣ) : ℂ :=
  Φ (a : F) * η a * (abv (a : F) : ℂ) ^ ((m : ℂ) * s)

variable [MeasurableSpace Fˣ]

/-- The actual scalar Mellin integral, before choosing a continuation. -/
def scalarMellinIntegral (abv : F → ℝ) (μ : Measure Fˣ) (η : Fˣ → ℂ)
    (m : ℕ) (Φ : SchwartzBruhat F) (s : ℂ) : ℂ :=
  ∫ a, scalarMellinIntegrand abv η m Φ s a ∂μ

/-- All continuations of all scalar tests for a fixed finite function. -/
def scalarMellinRationalValues (q : ℕ) (abv : F → ℝ) (μ : Measure Fˣ)
    (η : Fˣ → ℂ) (m : ℕ) : Set RationalFunctions :=
  {R | ∃ Φ : SchwartzBruhat F,
    HasRationalContinuation q (scalarMellinIntegral abv μ η m Φ) R}

/-- Scalar Mellin assertions, with one convergence threshold chosen before
all Schwartz--Bruhat tests and a common Laurent denominator. -/
def ScalarMellinAnalyticData (q : ℕ) (abv : F → ℝ) (μ : Measure Fˣ)
    (η : Fˣ → ℂ) (m : ℕ) : Prop :=
  (∃ c : ℝ, ∀ Φ : SchwartzBruhat F, ∀ s : ℂ, c < s.re →
    Integrable (scalarMellinIntegrand abv η m Φ s) μ) ∧
  (∀ Φ : SchwartzBruhat F, ∃ R : RationalFunctions,
    HasRationalContinuation q (scalarMellinIntegral abv μ η m Φ) R) ∧
  HasCommonDenominator (scalarMellinRationalValues q abv μ η m)

end Definitions

/-- The weighted normalized absolute value is an integer power of the spectral
point. Positivity of `q` fixes the logarithm branch. -/
private theorem mellin_natCast_zpow_cpow_eq (q : ℕ) (hq : 0 < q) (k : ℤ) (m : ℕ) (s : ℂ) :
    ((((q : ℝ) ^ (-k) : ℝ)) : ℂ) ^ ((m : ℂ) * s) = (spectralPoint q s ^ m) ^ k := by
  have harg : Complex.arg (q : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      Complex.arg_ofReal_of_nonneg (show 0 ≤ (q : ℝ) by positivity)
  rw [Complex.ofReal_zpow, Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
      (by simpa only [harg, mul_zero] using Real.pi_pos.le),
    spectralPoint, ← zpow_natCast, ← zpow_mul, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

/-- Positive powers of the spectral point are small on a right half-plane. -/
private theorem mellin_exists_re_threshold {q : ℕ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ c : ℝ, ∀ s : ℂ, c < s.re → ‖spectralPoint q s ^ m‖ < ρ := by
  set ρ1 := min ρ 1 with hρ1_def
  have hρ1 : 0 < ρ1 := lt_min hρ one_pos
  have hq0 : 0 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine ⟨-Real.log ρ1 / Real.log q, fun s hs => ?_⟩
  have hnorm : ‖spectralPoint q s‖ = (q : ℝ) ^ (-s.re) := by
    rw [spectralPoint, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re]
  have ht : (q : ℝ) ^ (-s.re) < ρ1 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hq0), ← Real.lt_log_iff_exp_lt hρ1]
    rw [div_lt_iff₀ hlogq] at hs
    linarith
  have ht0 : 0 ≤ (q : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  rw [norm_pow, hnorm]
  calc ((q : ℝ) ^ (-s.re)) ^ m ≤ (q : ℝ) ^ (-s.re) :=
        pow_le_of_le_one ht0 (ht.le.trans (min_le_right _ _)) hm.ne'
    _ < ρ1 := ht
    _ ≤ ρ := min_le_left _ _

private theorem mellin_normalizedAbs_cpow {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData)
    (a : F.Carrierˣ) (m : ℕ) (s : ℂ) :
    (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s) =
      (spectralPoint T.residueCardinality s ^ m) ^ T.ord (a : F.Carrier) := by
  rw [T.normalizedAbs_of_ne_zero a.ne_zero,
    mellin_natCast_zpow_cpow_eq T.residueCardinality (by
      have := T.residueCardinality_gt_one
      omega)]

/-- The shell theorem supplies a uniform half-plane, and the published
one-variable Mellin theorem supplies rationality and a common denominator. -/
theorem scalarMellinAnalyticData_finiteFunction
    (p : ℕ) [hp : Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel _
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace F.Carrierˣ := borel _
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∀ (m : ℕ), 0 < m → ∀ (η : F.Carrierˣ → ℂ), Continuous η →
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a))) →
      ScalarMellinAnalyticData T.residueCardinality T.normalizedAbs
        (localMultiplicativeHaar F.Carrier) η m := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  intro m hm η hη hfin
  obtain ⟨_, hrat, hden⟩ := oneVariableMellin p hp F T m hm η hη hfin
  refine ⟨?_, hrat, hden⟩
  obtain ⟨π, E, B, _, hB, htests⟩ := finiteFunctionShellSeries p hp F T η hη hfin
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨c, hc⟩ := mellin_exists_re_threshold T.residueCardinality_gt_one hm
    (one_div_pos.mpr hBpos)
  refine ⟨c, fun Φ s hs => ?_⟩
  obtain ⟨L, N, _, _, _, hI⟩ := htests Φ
  have hz : spectralPoint T.residueCardinality s ^ m ≠ 0 :=
    pow_ne_zero m (spectralPoint_ne_zero T.residueCardinality_gt_one s)
  have hsmall : B * ‖spectralPoint T.residueCardinality s ^ m‖ < 1 := by
    have h := (lt_div_iff₀ hBpos).mp (hc s hs)
    nlinarith
  change Integrable (fun a : F.Carrierˣ =>
    Φ (a : F.Carrier) * η a *
      (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s)) _
  simp_rw [mellin_normalizedAbs_cpow T]
  exact (hI _ hz hsmall).1

end Langlands.GodementJacquet
