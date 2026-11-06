import Langlands.Representation.GodementJacquet.TateCharacterDenominator
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof
import Mathlib.Topology.Algebra.IsOpenUnits

/-! Actual normalizing tests for scalar character Mellin integrals. -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @Quasicharacter F.Carrier _ T.topology
local notation "TestFunction" => @SchwartzBruhat F.Carrier T.topology

/-- The characteristic function of the actual valuation integer ring. -/
def characterIntegerRingTest : TestFunction := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.fieldT2
  exact Hecke.TestFunction.characteristic (s := (T.Integers : Set F.Carrier))
    ⟨Valuation.isClosed_integer, Valuation.isOpen_integer⟩
    (IsNonarchimedeanLocalField.isCompact_closedBall F.Carrier 1)

/-- The integer-ring test has exactly the one-sided geometric coefficients
for a character of conductor zero. -/
theorem characterIntegerRingTest_shell (χ : MultiplicativeCharacter)
    (hχ : T.multiplicativeConductor χ = 0)
    (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1) (n : ℤ) :
    characterShellCoefficient F T χ π (characterIntegerRingTest F T) n =
      if 0 ≤ n then (χ π : ℂ) ^ n else 0 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let K := integralUnits (ValuativeRel.valuation F.Carrier).integer
  have hKm : MeasurableSet (K : Set F.Carrierˣ) :=
    (integralUnits_isOpen _ Valuation.isOpen_integer).measurableSet
  have hord (u : F.Carrierˣ) (hu : u ∈ K) :
      T.ord ((π ^ n * u : F.Carrierˣ) : F.Carrier) = n := by
    rw [Units.val_mul, T.ord_mul (Units.ne_zero _) u.ne_zero,
      Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ, mul_one,
      (mem_integralUnits_iff_ord_zero F T u).mp hu, add_zero]
  have hmem (u : F.Carrierˣ) (hu : u ∈ K) :
      ((π ^ n * u : F.Carrierˣ) : F.Carrier) ∈ T.Integers ↔ 0 ≤ n := by
    rw [← T.normalizedAbs_le_one_iff_mem_integers,
      T.normalizedAbs_of_ne_zero (Units.ne_zero _), hord u hu,
      zpow_le_one_iff_right₀ (show (1 : ℝ) < T.residueCardinality by
        exact_mod_cast T.residueCardinality_gt_one)]
    omega
  have htriv := (conductor_zero_iff_integralUnits F T χ).mp hχ
  unfold characterShellCoefficient
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left hn]
    calc
      _ = ∫ _u in (K : Set F.Carrierˣ), (χ π : ℂ) ^ n
          ∂localMultiplicativeHaar F.Carrier := by
        refine setIntegral_congr_fun hKm fun u hu => ?_
        change (T.Integers : Set F.Carrier).indicator (fun _ => (1 : ℂ)) _ * _ = _
        rw [Set.indicator_of_mem ((hmem u hu).mpr hn), one_mul, map_mul, map_zpow,
          htriv u hu]
        simp
      _ = _ := by simp [K, measureReal_def]
  · rw [ite_eq_right hn]
    calc
      _ = ∫ _u in (K : Set F.Carrierˣ), (0 : ℂ)
          ∂localMultiplicativeHaar F.Carrier := by
        refine setIntegral_congr_fun hKm fun u hu => ?_
        change (T.Integers : Set F.Carrier).indicator (fun _ => (1 : ℂ)) _ * _ = _
        rw [Set.indicator_of_notMem (fun h => hn ((hmem u hu).mp h)), zero_mul]
      _ = _ := integral_zero _ _

/-- The bilateral sum for the integer-ring test is the geometric reciprocal. -/
theorem characterIntegerRingTest_tsum (χ : MultiplicativeCharacter)
    (hχ : T.multiplicativeConductor χ = 0)
    (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (z : ℂ) (hz : ‖(χ π : ℂ) * z‖ < 1) :
    Summable (fun n : ℤ =>
      characterShellCoefficient F T χ π (characterIntegerRingTest F T) n * z ^ n) ∧
      ∑' n : ℤ,
        characterShellCoefficient F T χ π (characterIntegerRingTest F T) n * z ^ n =
          (1 - (χ π : ℂ) * z)⁻¹ := by
  have htail : (fun j : ℕ =>
      characterShellCoefficient F T χ π (characterIntegerRingTest F T)
        ((j : ℤ) + (0 : ℕ)) * z ^ ((j : ℤ) + (0 : ℕ))) =
        (fun j : ℕ => ((χ π : ℂ) * z) ^ j) := by
    funext j
    rw [characterIntegerRingTest_shell F T χ hχ π hπ]
    simp [mul_pow]
  obtain ⟨hsum, htsum⟩ :=
    Langlands.Analysis.EventuallyRecurrentLaurentSeries.summable_and_tsum_split
      (fun n : ℤ =>
        characterShellCoefficient F T χ π (characterIntegerRingTest F T) n * z ^ n)
      0 0 (fun n hn => by
        rw [characterIntegerRingTest_shell F T χ hχ π hπ]
        simp [show ¬0 ≤ n by omega])
      (htail ▸ (summable_geometric_of_norm_lt_one hz))
  refine ⟨hsum, ?_⟩
  rw [htail, tsum_geometric_of_norm_lt_one hz] at htsum
  simpa using htsum

/-- For conductor zero, the actual integer-ring test continues to the
specified reciprocal abelian Euler polynomial. -/
theorem characterIntegerRingTest_continuation (χ : MultiplicativeCharacter)
    (hχ : T.multiplicativeConductor χ = 0) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel _
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace F.Carrierˣ := borel _
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    HasRationalContinuation T.residueCardinality
      (scalarMellinIntegral T.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun a => (χ a : ℂ)) 1 (characterIntegerRingTest F T))
      (LocalFactor.PadicAbelian.rationalLFactor T χ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  have hη : Continuous (fun a : F.Carrierˣ => (χ a : ℂ)) :=
    Units.continuous_val.comp χ.continuous
  obtain ⟨π, _, B, hπ, hB, hShellTests⟩ := finiteFunctionShellSeries p inferInstance F T
    (fun a => (χ a : ℂ)) hη (tateCharacter_translationFinite χ)
  obtain ⟨_, _, _, _, _, hIntegral⟩ := hShellTests (characterIntegerRingTest F T)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hχpos : 0 < ‖(χ π : ℂ)‖ := norm_pos_iff.mpr (χ π).ne_zero
  obtain ⟨c, hc⟩ := character_spectral_threshold T.residueCardinality_gt_one
    (lt_min (one_div_pos.mpr hBpos) (one_div_pos.mpr hχpos))
  refine ⟨c, fun s hs => ?_⟩
  let z := spectralPoint T.residueCardinality s
  have hz : z ≠ 0 := spectralPoint_ne_zero T.residueCardinality_gt_one s
  have hsmall := hc s hs
  have hsmallB : B * ‖z‖ < 1 := by
    have h := (lt_div_iff₀ hBpos).mp (hsmall.trans_le (min_le_left _ _))
    nlinarith
  have hsmallχ : ‖(χ π : ℂ) * z‖ < 1 := by
    rw [norm_mul]
    have h := (lt_div_iff₀ hχpos).mp (hsmall.trans_le (min_le_right _ _))
    nlinarith
  have hnot : (χ π : ℂ) * z ≠ 1 := by
    intro h
    simp [h] at hsmallχ
  have hv := congrArg (fun u : ℂˣ => (u : ℂ))
    (unramified_character_order_one F T χ hχ π hπ)
  have hDeval : (LocalFactor.PadicAbelian.lPolynomial T χ).eval z =
      1 - (χ π : ℂ) * z := by
    simp [LocalFactor.PadicAbelian.lPolynomial, hχ, ← hv]
  have hD : (LocalFactor.PadicAbelian.lPolynomial T χ).eval z ≠ 0 := by
    rw [hDeval]
    exact sub_ne_zero.mpr (Ne.symm hnot)
  obtain ⟨hreg, heval⟩ := regular_and_eval_div z 1
    (LocalFactor.PadicAbelian.lPolynomial T χ) hD
  have hI := hIntegral z hz hsmallB
  have hsum := characterIntegerRingTest_tsum F T χ hχ π hπ z hsmallχ
  refine ⟨?_, ?_⟩
  · simpa only [map_one, one_div, LocalFactor.PadicAbelian.rationalLFactor] using hreg
  · calc
      _ = ∑' n : ℤ,
          characterShellCoefficient F T χ π (characterIntegerRingTest F T) n * z ^ n := by
        simp only [scalarMellinIntegral, scalarMellinIntegrand, Nat.cast_one, one_mul]
        simp_rw [character_normalizedAbs_cpow F T]
        exact hI.2.2
      _ = (1 - (χ π : ℂ) * z)⁻¹ := hsum.2
      _ = _ := by
        simpa only [Polynomial.eval_one, hDeval, one_div, map_one,
          LocalFactor.PadicAbelian.rationalLFactor] using heval.symm

/-- Every continuous character admits an actual compact-open test whose
Mellin integral converges and equals one for every complex parameter. -/
theorem exists_scalarMellinIntegral_one (χ : MultiplicativeCharacter) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
  let := T.fieldT2
    let : MeasurableSpace F.Carrier := borel _
    let : BorelSpace F.Carrier := ⟨rfl⟩
    let : MeasurableSpace F.Carrierˣ := borel _
    let : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∃ Φ : TestFunction, ∀ s : ℂ,
      Integrable (scalarMellinIntegrand T.normalizedAbs (fun a => (χ a : ℂ)) 1 Φ s)
        (localMultiplicativeHaar F.Carrier) ∧
      scalarMellinIntegral T.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun a => (χ a : ℂ)) 1 Φ s = 1 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let K₀ := integralUnitsOpen (ValuativeRel.valuation F.Carrier).integer
    Valuation.isOpen_integer
  let J : OpenSubgroup F.Carrierˣ :=
    { toSubgroup := K₀.toSubgroup ⊓ χ.toMonoidHom.ker
      isOpen' := K₀.isOpen.inter (T.quasicharacter_isOpen_ker χ) }
  have hJc : IsCompact (J : Set F.Carrierˣ) :=
    (integralUnits_isCompact (ValuativeRel.valuation F.Carrier).integer).of_isClosed_subset
      J.isClosed (fun _ h => h.1)
  let U : Set F.Carrier := Units.val '' (J : Set F.Carrierˣ)
  have hUc : IsCompact U := hJc.image Units.continuous_val
  have hUo : IsOpen U := IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ J.isOpen
  have hmem (a : F.Carrierˣ) : (a : F.Carrier) ∈ U ↔ a ∈ J := by
    constructor
    · rintro ⟨b, hb, he⟩
      exact Units.val_injective he ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  let μ := localMultiplicativeHaar F.Carrier
  have hJm : MeasurableSet (J : Set F.Carrierˣ) := J.isOpen.measurableSet
  have hJfin : μ (J : Set F.Carrierˣ) ≠ ⊤ := hJc.measure_lt_top.ne
  have hJpos : μ (J : Set F.Carrierˣ) ≠ 0 :=
    (J.isOpen.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hmass : (μ.real (J : Set F.Carrierˣ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hJpos, hJfin⟩
  let c : ℂ := (μ.real (J : Set F.Carrierˣ) : ℂ)⁻¹
  let Φ : TestFunction :=
    c • Hecke.TestFunction.characteristic ⟨hUc.isClosed, hUo⟩ hUc
  have hpt (s : ℂ) :
      scalarMellinIntegrand T.normalizedAbs (fun a => (χ a : ℂ)) 1 Φ s =
        (J : Set F.Carrierˣ).indicator (fun _ => c) := by
    funext a
    by_cases ha : a ∈ J
    · have hΦ : Φ (a : F.Carrier) = c := by
        change c * U.indicator (fun _ => (1 : ℂ)) (a : F.Carrier) = c
        rw [Set.indicator_of_mem ((hmem a).mpr ha), mul_one]
      have habs : T.normalizedAbs (a : F.Carrier) = 1 :=
        (T.ord_eq_zero_iff_normalizedAbs a).mp
          ((mem_integralUnits_iff_ord_zero F T a).mp ha.1)
      have hχ : χ a = 1 := ha.2
      simp [scalarMellinIntegrand, hΦ, habs, hχ, Set.indicator_of_mem ha]
    · have hΦ : Φ (a : F.Carrier) = 0 := by
        change c * U.indicator (fun _ => (1 : ℂ)) (a : F.Carrier) = 0
        rw [Set.indicator_of_notMem (fun h => ha ((hmem a).mp h)), mul_zero]
      simp [scalarMellinIntegrand, hΦ, Set.indicator_of_notMem ha]
  refine ⟨Φ, fun s => ⟨?_, ?_⟩⟩
  · rw [hpt]
    exact (integrable_indicator_iff hJm).mpr (integrableOn_const (C := c) hJfin)
  · unfold scalarMellinIntegral
    rw [hpt, integral_indicator_const c hJm]
    change (μ.real (J : Set F.Carrierˣ) : ℂ) *
      (μ.real (J : Set F.Carrierˣ) : ℂ)⁻¹ = 1
    exact mul_inv_cancel₀ hmass

/-- The unit is attained before taking the Laurent span of scalar values. -/
theorem one_mem_scalarMellinRationalValues (χ : MultiplicativeCharacter) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
  let := T.fieldT2
    let : MeasurableSpace F.Carrier := borel _
    let : BorelSpace F.Carrier := ⟨rfl⟩
    let : MeasurableSpace F.Carrierˣ := borel _
    let : BorelSpace F.Carrierˣ := ⟨rfl⟩
    (1 : RationalFunctions) ∈ scalarMellinRationalValues T.residueCardinality
      T.normalizedAbs (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  obtain ⟨Φ, hΦ⟩ := exists_scalarMellinIntegral_one F T χ
  exact ⟨Φ, 0, fun s _ => by simpa using (hΦ s).2⟩

/-- The specified reciprocal is attained by an actual scalar test in both
conductor branches. -/
theorem rationalLFactor_mem_scalarMellinRationalValues (χ : MultiplicativeCharacter) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel _
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace F.Carrierˣ := borel _
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    LocalFactor.PadicAbelian.rationalLFactor T χ ∈
      scalarMellinRationalValues T.residueCardinality
        T.normalizedAbs (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  by_cases hχ : T.multiplicativeConductor χ = 0
  · exact ⟨characterIntegerRingTest F T, characterIntegerRingTest_continuation F T χ hχ⟩
  · simpa [LocalFactor.PadicAbelian.rationalLFactor,
      LocalFactor.PadicAbelian.lPolynomial, hχ] using one_mem_scalarMellinRationalValues F T χ

/-- The abelian Euler polynomial is the normalized generator of the Laurent
span of the actual scalar character Mellin values. -/
theorem scalarMellin_character_isNormalizedGenerator (χ : MultiplicativeCharacter) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel _
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace F.Carrierˣ := borel _
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    IsNormalizedGenerator
      (scalarMellinRationalValues T.residueCardinality T.normalizedAbs
        (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1)
      (LocalFactor.PadicAbelian.lPolynomial T χ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel _
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  apply (isNormalizedGenerator_iff _ _).2
  refine ⟨LocalFactor.PadicAbelian.lPolynomial_coeff_zero T χ, ?_, ?_⟩
  · rintro R ⟨Φ, hR⟩
    exact scalarMellin_character_denominator F T χ Φ R hR
  · exact mem_zetaSpan (rationalLFactor_mem_scalarMellinRationalValues F T χ)

end Langlands.GodementJacquet
