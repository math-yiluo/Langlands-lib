import Langlands.Representation.GodementJacquet.TateCharacterShells
import Langlands.Representation.GodementJacquet.TateMatrixAnalyticData
import Langlands.LocalFactor.Abelian.Padic

/-! The exact abelian Euler polynomial clears character Mellin denominators. -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @Quasicharacter F.Carrier _ T.topology
local notation "TestFunction" => @SchwartzBruhat F.Carrier T.topology

/-- Unramified characters take the same value at every order-one element. -/
theorem unramified_character_order_one (χ : MultiplicativeCharacter)
    (hχ : T.multiplicativeConductor χ = 0)
    (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1) :
    χ π = χ (LocalFactor.PadicAbelian.uniformizerUnit T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let a := LocalFactor.PadicAbelian.uniformizerUnit T
  have ha : T.ord (a : F.Carrier) = 1 :=
    LocalFactor.PadicAbelian.uniformizerUnit_ord T
  have hk : π * a⁻¹ ∈ RankinSelberg.integralUnits
      (ValuativeRel.valuation F.Carrier).integer := by
    rw [mem_integralUnits_iff_ord_zero F T]
    rw [Units.val_mul, T.ord_mul π.ne_zero (Units.ne_zero _), Units.val_inv_eq_inv_val,
      T.ord_inv, hπ, ha]
    norm_num
  have he := (conductor_zero_iff_integralUnits F T χ).mp hχ _ hk
  simpa only [map_mul, map_inv, mul_inv_eq_one] using he

/-- The exact scalar character recurrence: geometric in conductor zero,
and the order-zero recurrence otherwise. -/
def characterShellRecurrence (χ : MultiplicativeCharacter) : LinearRecurrence ℂ :=
  if T.multiplicativeConductor χ = 0 then
    ⟨1, fun _ => (χ (LocalFactor.PadicAbelian.uniformizerUnit T) : ℂ)⟩
  else ⟨0, Fin.elim0⟩

/-- Its reverse characteristic polynomial is the specified abelian denominator. -/
theorem characterShellRecurrence_polynomial (χ : MultiplicativeCharacter) :
    (1 - ∑ i : Fin (characterShellRecurrence F T χ).order,
      Polynomial.C ((characterShellRecurrence F T χ).coeffs i) *
        Polynomial.X ^ ((characterShellRecurrence F T χ).order - i.val)) =
      LocalFactor.PadicAbelian.lPolynomial T χ := by
  classical
  by_cases hχ : T.multiplicativeConductor χ = 0
  · have hE : characterShellRecurrence F T χ =
        (⟨1, fun _ => (χ (LocalFactor.PadicAbelian.uniformizerUnit T) : ℂ)⟩ :
          LinearRecurrence ℂ) := by simp [characterShellRecurrence, hχ]
    rw [hE]
    simp [LocalFactor.PadicAbelian.lPolynomial, hχ]
  · have hE : characterShellRecurrence F T χ =
        (⟨0, Fin.elim0⟩ : LinearRecurrence ℂ) := by
      simp [characterShellRecurrence, hχ]
    rw [hE]
    simp [LocalFactor.PadicAbelian.lPolynomial, hχ]

/-- Every actual character shell sequence eventually satisfies the exact
recurrence, from any larger natural cutoff. -/
theorem characterShellCoefficient_recurrence (χ : MultiplicativeCharacter)
    (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (Φ : TestFunction) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      (characterShellRecurrence F T χ).IsSolution
        (fun j : ℕ => characterShellCoefficient F T χ π Φ ((j : ℤ) + M)) := by
  classical
  obtain ⟨N, hN⟩ := characterShellCoefficient_eventual F T χ π hπ Φ
  refine ⟨N, fun M hM => ?_⟩
  by_cases hχ : T.multiplicativeConductor χ = 0
  · have hv := congrArg (fun u : ℂˣ => (u : ℂ))
      (unramified_character_order_one F T χ hχ π hπ)
    have hE : characterShellRecurrence F T χ =
        (⟨1, fun _ => (χ (LocalFactor.PadicAbelian.uniformizerUnit T) : ℂ)⟩ :
          LinearRecurrence ℂ) := by simp [characterShellRecurrence, hχ]
    rw [hE]
    intro j
    simp only [Fin.sum_univ_one]
    change characterShellCoefficient F T χ π Φ (((j + 1 : ℕ) : ℤ) + M) =
      (χ (LocalFactor.PadicAbelian.uniformizerUnit T) : ℂ) *
        characterShellCoefficient F T χ π Φ ((j : ℤ) + M)
    rw [hN _ (by omega), hN _ (by omega), ite_eq_left hχ, ite_eq_left hχ, ← hv]
    have hz : (χ π : ℂ) ≠ 0 := (χ π).ne_zero
    rw [show (((j + 1 : ℕ) : ℤ) + M) = ((j : ℤ) + M) + 1 by omega,
      zpow_add₀ hz, zpow_one]
    ring
  · have hE : characterShellRecurrence F T χ =
        (⟨0, Fin.elim0⟩ : LinearRecurrence ℂ) := by
      simp [characterShellRecurrence, hχ]
    rw [hE]
    intro j
    simp only [Fin.sum_univ_zero, Nat.add_zero]
    rw [hN _ (by omega), ite_eq_right hχ]

theorem character_normalizedAbs_cpow (a : F.Carrierˣ) (s : ℂ) :
    (T.normalizedAbs (a : F.Carrier) : ℂ) ^ s =
      spectralPoint T.residueCardinality s ^ T.ord (a : F.Carrier) := by
  have harg : Complex.arg (T.residueCardinality : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using Complex.arg_ofReal_of_nonneg
      (show 0 ≤ (T.residueCardinality : ℝ) by positivity)
  rw [T.normalizedAbs_of_ne_zero a.ne_zero, Complex.ofReal_zpow, Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
      (by simpa only [harg, mul_zero] using Real.pi_pos.le),
    spectralPoint, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

theorem character_spectral_threshold {q : ℕ} (hq : 1 < q) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re → ‖spectralPoint q s‖ < ρ := by
  have hq0 : 0 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine ⟨-Real.log ρ / Real.log q, fun s hs => ?_⟩
  rw [spectralPoint, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re,
    Real.rpow_def_of_pos (by exact_mod_cast hq0), ← Real.lt_log_iff_exp_lt hρ]
  rw [div_lt_iff₀ hlogq] at hs
  linarith

/-- The specified abelian Euler polynomial clears every rational continuation
of every actual scalar character Mellin integral. -/
theorem scalarMellin_character_denominator (χ : MultiplicativeCharacter) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel _
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace F.Carrierˣ := borel _
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∀ (Φ : TestFunction) (R : RationalFunctions),
      HasRationalContinuation T.residueCardinality
        (scalarMellinIntegral T.normalizedAbs (localMultiplicativeHaar F.Carrier)
          (fun a => (χ a : ℂ)) 1 Φ) R →
      ∃ P : LaurentPolynomial ℂ,
        laurentToRatFunc P =
          algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (LocalFactor.PadicAbelian.lPolynomial T χ) * R := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  intro Φ R hR
  have hη : Continuous (fun a : F.Carrierˣ => (χ a : ℂ)) :=
    Units.continuous_val.comp χ.continuous
  obtain ⟨π, _, B, hπ, hB, hShellTests⟩ := finiteFunctionShellSeries p inferInstance F T
    (fun a => (χ a : ℂ)) hη (tateCharacter_translationFinite χ)
  obtain ⟨_, ρ, hρ, hWeights⟩ :=
    Langlands.Analysis.eventuallyRecurrentLaurentSeriesStatement_proof
      (characterShellRecurrence F T χ)
  dsimp only at hWeights
  rw [characterShellRecurrence_polynomial F T χ] at hWeights
  obtain ⟨_, hRepresent⟩ := hWeights 1 (by omega)
  simp only [pow_one, Polynomial.comp_X] at hRepresent
  obtain ⟨L, N, hLN, hlow, _, hIntegral⟩ := hShellTests Φ
  obtain ⟨Nχ, hχrec⟩ := characterShellCoefficient_recurrence F T χ π hπ Φ
  let M := max N Nχ
  have hLM : L ≤ (M : ℤ) := le_trans hLN (by exact_mod_cast le_max_left N Nχ)
  obtain ⟨S, P, hclear, hEval⟩ :=
    hRepresent _ L M hLM hlow (hχrec M (le_max_right N Nχ))
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨c, hc⟩ := character_spectral_threshold T.residueCardinality_gt_one
    (lt_min (one_div_pos.mpr hBpos) hρ)
  have hS : HasRationalContinuation T.residueCardinality
      (scalarMellinIntegral T.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun a => (χ a : ℂ)) 1 Φ) S := by
    refine ⟨c, fun s hs => ?_⟩
    have hz := spectralPoint_ne_zero T.residueCardinality_gt_one s
    have hsmall := hc s hs
    have hsmallB : B * ‖spectralPoint T.residueCardinality s‖ < 1 := by
      have h := (lt_div_iff₀ hBpos).mp (hsmall.trans_le (min_le_left _ _))
      nlinarith
    have hI := hIntegral _ hz hsmallB
    have hE := hEval _ hz (hsmall.trans_le (min_le_right _ _))
    refine ⟨hE.2.1, ?_⟩
    simp only [scalarMellinIntegral, scalarMellinIntegrand, Nat.cast_one, one_mul]
    simp_rw [character_normalizedAbs_cpow F T]
    exact hI.2.2.trans hE.2.2
  refine ⟨P, ?_⟩
  rw [hR.unique T.residueCardinality_gt_one hS]
  simpa only [laurentToRatFunc_toLaurent] using hclear

end Langlands.GodementJacquet
