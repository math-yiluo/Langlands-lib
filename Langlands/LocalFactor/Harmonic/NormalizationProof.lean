import Langlands.LocalFactor.Harmonic.DualityProof
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Integer-ring volume criteria for duality and self-duality. -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.LocalFactors

universe u

private theorem normalization_plus_eq {K : Type*} [CommRing K] [MeasurableSpace K]
    (ψ : AddChar K Circle) (μ : Measure K) (f : K → ℂ) (y : K) :
    Fourier.fourierIntegral ψ⁻¹ μ f y =
      ∫ x, (ψ (x * y) : ℂ) * f x ∂μ := by
  simp only [Fourier.fourierIntegral_def, AddChar.inv_apply, neg_neg,
    Circle.smul_def, smul_eq_mul]

private theorem normalization_const_mul {K : Type*} [CommRing K] [MeasurableSpace K]
    (ψ : AddChar K Circle) (μ : Measure K) (c : ℂ) (f : K → ℂ) (y : K) :
    Fourier.fourierIntegral ψ⁻¹ μ (fun x => c * f x) y =
      c * Fourier.fourierIntegral ψ⁻¹ μ f y := by
  simp only [normalization_plus_eq, mul_left_comm (ψ _ : ℂ) c, integral_const_mul]

section SuppliedTopology

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

open HarmonicAnalysis

private def NormalizationDual {K : Type*} [CommRing K] [TopologicalSpace K]
    [MeasurableSpace K] (ψ : AddChar K Circle) (μ ν : Measure K) : Prop :=
  ∀ (f : K → ℂ), IsLocallyConstant f → HasCompactSupport f →
    ∀ x, Fourier.fourierIntegral ψ⁻¹ ν
      (Fourier.fourierIntegral ψ⁻¹ μ f) x = f (-x)

private theorem integer_mass_pos :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (μ : Measure F.Carrier) [μ.IsAddHaarMeasure],
    0 < (μ (T.Integers : Set F.Carrier)).toReal := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro μ _
  exact ENNReal.toReal_pos
    (T.isOpen_integers.measure_pos μ ⟨0, T.Integers.zero_mem⟩).ne'
    T.isCompact_integers.measure_ne_top

private theorem haar_eq_of_integer_mass :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (μ ν : Measure F.Carrier)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (_h : (μ (T.Integers : Set F.Carrier)).toReal =
      (ν (T.Integers : Set F.Carrier)).toReal), μ = ν := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro μ ν _ _ h
  let c : ℝ≥0 := μ.addHaarScalarFactor ν
  have he : μ = c • ν := Measure.isAddLeftInvariant_eq_smul μ ν
  have hm := congrArg (fun ξ : Measure F.Carrier =>
    (ξ (T.Integers : Set F.Carrier)).toReal) he
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal, h] at hm
  have hc : (c : ℝ) = 1 := by
    nlinarith [integer_mass_pos T ν]
  have hc' : c = 1 := NNReal.eq hc
  simpa only [hc', one_smul] using he

private theorem lattice_indicator_fourier :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure F.Carrier) [μ.IsAddHaarMeasure] (m : ℤ) (y : F.Carrier),
    Fourier.fourierIntegral ψ.toAddChar⁻¹ μ
      ((T.additiveLattice m : Set F.Carrier).indicator (fun _ => (1 : ℂ))) y =
      ((μ (T.additiveLattice m : Set F.Carrier)).toReal : ℂ) *
        (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ)) y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro ψ μ _ m y
  let μb : AdditiveHaarMeasure F.Carrier := ⟨μ, inferInstance, inferInstance⟩
  have h := ((padicLatticeFourier F T) ψ μb m 0 y).2
  have hset : {x : F.Carrier | x ∈ T.additiveLattice m} =
      (T.additiveLattice m : Set F.Carrier) := by ext x; rfl
  simpa only [normalization_plus_eq, fourierIntegral, μb,
    UnitaryAdditiveCharacter.complex_apply, sub_zero, hset, zero_mul,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one] using h

private theorem integer_indicator_fourier :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure F.Carrier) [μ.IsAddHaarMeasure] (y : F.Carrier),
    Fourier.fourierIntegral ψ.toAddChar⁻¹ μ
      ((T.Integers : Set F.Carrier).indicator (fun _ => (1 : ℂ))) y =
      ((μ (T.Integers : Set F.Carrier)).toReal : ℂ) *
        (T.additiveLattice (T.additiveConductor ψ) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ)) y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro ψ μ _ y
  have hzero : (T.additiveLattice 0 : Set F.Carrier) =
      (T.Integers : Set F.Carrier) := Set.ext T.mem_additiveLattice_zero
  simpa only [hzero, sub_zero] using lattice_indicator_fourier T ψ μ 0 y

private theorem dual_integer_mass :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ ν : Measure F.Carrier) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (_h : NormalizationDual ψ.toAddChar μ ν),
    (μ (T.Integers : Set F.Carrier)).toReal *
      (ν (T.Integers : Set F.Carrier)).toReal =
        (T.residueCardinality : ℝ) ^ (-T.additiveConductor ψ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  let := T.fieldT2
  intro ψ μ ν _ _ h
  let O : Set F.Carrier := T.Integers
  let g : F.Carrier → ℂ := O.indicator (fun _ => 1)
  have hlc : IsLocallyConstant g :=
    (Hecke.TestFunction.characteristic
      ⟨T.isCompact_integers.isClosed, T.isOpen_integers⟩ T.isCompact_integers).locallyConstant
  have hc : HasCompactSupport g :=
    (Hecke.TestFunction.characteristic
      ⟨T.isCompact_integers.isClosed, T.isOpen_integers⟩ T.isCompact_integers).hasCompactSupport
  have he := h g hlc hc 0
  have hg : Fourier.fourierIntegral ψ.toAddChar⁻¹ μ g =
      fun y => ((μ O).toReal : ℂ) *
        (T.additiveLattice (T.additiveConductor ψ) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ)) y := funext (integer_indicator_fourier T ψ μ)
  rw [hg, normalization_const_mul, lattice_indicator_fourier,
    Set.indicator_of_mem (show (0 : F.Carrier) ∈ T.additiveLattice
      (T.additiveConductor ψ - T.additiveConductor ψ) from (T.additiveLattice _).zero_mem),
    mul_one, neg_zero] at he
  have hg0 : g 0 = 1 := Set.indicator_of_mem T.Integers.zero_mem _
  rw [hg0] at he
  let νb : AdditiveHaarMeasure F.Carrier := ⟨ν, inferInstance, inferInstance⟩
  have hm := ((padicLatticeHaar F T).1 νb (T.additiveConductor ψ)).2.2
  have hzero : (T.additiveLattice 0 : Set F.Carrier) =
      (T.Integers : Set F.Carrier) := Set.ext T.mem_additiveLattice_zero
  change (ν (T.additiveLattice (T.additiveConductor ψ) : Set F.Carrier)).toReal = _ at hm
  rw [hzero] at hm
  rw [hm] at he
  have he' : (μ O).toReal * ((T.residueCardinality : ℝ) ^ T.additiveConductor ψ *
      (ν O).toReal) = 1 := by exact_mod_cast he
  have hq : 0 < (T.residueCardinality : ℝ) := by
    exact_mod_cast lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  rw [zpow_neg]
  apply (mul_right_cancel₀ (zpow_ne_zero _ hq.ne'))
  rw [inv_mul_cancel₀ (zpow_ne_zero _ hq.ne')]
  nlinarith [he']

private theorem dual_iff_integer_mass :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ ν : Measure F.Carrier) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure],
    NormalizationDual ψ.toAddChar μ ν ↔
      (μ (T.Integers : Set F.Carrier)).toReal *
        (ν (T.Integers : Set F.Carrier)).toReal =
          (T.residueCardinality : ℝ) ^ (-T.additiveConductor ψ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro ψ μ ν _ _
  constructor
  · exact dual_integer_mass T ψ μ ν
  · intro hm
    obtain ⟨htd, hd⟩ := padicFourierDuality p F T
    let := htd
    obtain ⟨ρ, hρ, _⟩ := (hd ψ.toAddChar ψ.continuous_toFun ψ.nontrivial).1 μ inferInstance
    let := hρ.1
    have hρm := dual_integer_mass T ψ μ ρ hρ.2
    have he : (ν (T.Integers : Set F.Carrier)).toReal =
        (ρ (T.Integers : Set F.Carrier)).toReal :=
      mul_left_cancel₀ (integer_mass_pos T μ).ne' (hm.trans hρm.symm)
    rw [haar_eq_of_integer_mass T ν ρ he]
    exact hρ.2

private theorem normalization_card_pos : 0 < (T.residueCardinality : ℝ) := by
  exact_mod_cast lt_trans Nat.zero_lt_one T.residueCardinality_gt_one

private theorem normalization_half_square (n : ℤ) :
    (T.residueCardinality : ℝ) ^ (-(n : ℝ) / 2) *
      (T.residueCardinality : ℝ) ^ (-(n : ℝ) / 2) =
        (T.residueCardinality : ℝ) ^ (-n) := by
  rw [← Real.rpow_add (normalization_card_pos T), ← Real.rpow_intCast, Int.cast_neg]
  congr 1
  ring

private theorem self_dual_iff_integer_mass :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure F.Carrier) [μ.IsAddHaarMeasure],
    NormalizationDual ψ.toAddChar μ μ ↔
      μ (T.Integers : Set F.Carrier) =
        ENNReal.ofReal ((T.residueCardinality : ℝ) ^
          (-(T.additiveConductor ψ : ℝ) / 2)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro ψ μ _
  rw [dual_iff_integer_mass T ψ μ μ]
  have hs := Real.rpow_pos_of_pos (normalization_card_pos T)
    (-(T.additiveConductor ψ : ℝ) / 2)
  constructor
  · intro hm
    have hv := (mul_self_inj_of_nonneg (integer_mass_pos T μ).le hs.le).mp
      (hm.trans (normalization_half_square T _).symm)
    rw [← ENNReal.ofReal_toReal
      (T.isCompact_integers.measure_ne_top (μ := μ)), hv]
  · intro hm
    rw [hm, ENNReal.toReal_ofReal hs.le]
    exact normalization_half_square T _

private theorem integer_indicator_fourier_uniformizer :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure F.Carrier) [μ.IsAddHaarMeasure] (y : F.Carrier),
    Fourier.fourierIntegral ψ.toAddChar⁻¹ μ
      ((T.Integers : Set F.Carrier).indicator (fun _ => (1 : ℂ))) y =
      ((μ (T.Integers : Set F.Carrier)).toReal : ℂ) *
        (T.Integers : Set F.Carrier).indicator (fun _ => (1 : ℂ))
          (T.uniformizer ^ T.additiveConductor ψ * y) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ _ y
  rw [integer_indicator_fourier T ψ μ]
  have hm : y ∈ T.additiveLattice (T.additiveConductor ψ) ↔
      T.uniformizer ^ T.additiveConductor ψ * y ∈ T.Integers := by
    simpa only [zpow_neg, div_inv_eq_mul, mul_comm] using
      T.mem_additiveLattice_iff_div_mem_integers (T.additiveConductor ψ) y
  congr 1
  classical
  by_cases hy : y ∈ T.additiveLattice (T.additiveConductor ψ)
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hm.mp hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (mt hm.mpr hy)]

private theorem fixed_haar_ratio :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ σ : Measure F.Carrier) [μ.IsAddHaarMeasure] [σ.IsAddHaarMeasure],
    NormalizationDual ψ.toAddChar σ σ →
    μ = ENNReal.ofReal
      ((T.residueCardinality : ℝ) ^ ((T.additiveConductor ψ : ℝ) / 2) *
        (μ (T.Integers : Set F.Carrier)).toReal) • σ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro ψ μ σ _ _ hσ
  let c := (T.residueCardinality : ℝ) ^ ((T.additiveConductor ψ : ℝ) / 2) *
    (μ (T.Integers : Set F.Carrier)).toReal
  have hc : 0 < c := mul_pos
    (Real.rpow_pos_of_pos (normalization_card_pos T) _) (integer_mass_pos T μ)
  let : (ENNReal.ofReal c • σ).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul σ (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top
  apply haar_eq_of_integer_mass T μ (ENNReal.ofReal c • σ)
  have hs := (self_dual_iff_integer_mass T ψ σ).mp hσ
  have hcancel : (T.residueCardinality : ℝ) ^ ((T.additiveConductor ψ : ℝ) / 2) *
      (T.residueCardinality : ℝ) ^ (-(T.additiveConductor ψ : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (normalization_card_pos T)]
    have he : (T.additiveConductor ψ : ℝ) / 2 +
        -(T.additiveConductor ψ : ℝ) / 2 = 0 := by ring
    rw [he, Real.rpow_zero]
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc.le, hs,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (normalization_card_pos T) _).le]
  dsimp [c]
  rw [mul_right_comm, hcancel, one_mul]

private theorem self_dual_character_scaling :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure F.Carrier) [μ.IsAddHaarMeasure],
    NormalizationDual ψ.toAddChar μ μ → ∀ a : F.Carrierˣ,
    NormalizationDual (ψ.toAddChar.mulShift (a : F.Carrier))
      (ENNReal.ofReal (Real.sqrt (T.normalizedAbs (a : F.Carrier))) • μ)
      (ENNReal.ofReal (Real.sqrt (T.normalizedAbs (a : F.Carrier))) • μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro ψ μ _ hμ a
  let χ : UnitaryAdditiveCharacter F.Carrier :=
    ⟨ψ.toAddChar.mulShift (a : F.Carrier),
      ψ.continuous_toFun.comp (continuous_const.mul continuous_id),
      (AddChar.mulShift_unit_eq_one_iff ψ.toAddChar a.isUnit).not.mpr ψ.nontrivial⟩
  have hc : T.additiveConductor χ = T.additiveConductor ψ + T.ord (a : F.Carrier) :=
    (T.isGreatest_fractionalIdeal_triviality χ).unique
      ((padicAdditiveConductor p F T ψ.toAddChar ψ.continuous_toFun ψ.nontrivial).2.1
        _ (T.isGreatest_fractionalIdeal_triviality ψ) a)
  have hrpos : 0 < Real.sqrt (T.normalizedAbs (a : F.Carrier)) :=
    Real.sqrt_pos.mpr (T.normalizedAbs_pos a.ne_zero)
  let : (ENNReal.ofReal (Real.sqrt (T.normalizedAbs (a : F.Carrier))) • μ).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ (ENNReal.ofReal_ne_zero_iff.mpr hrpos)
      ENNReal.ofReal_ne_top
  apply (dual_iff_integer_mass T χ _ _).mpr
  have hm := dual_integer_mass T ψ μ μ hμ
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hrpos.le, hc]
  calc
    _ = (Real.sqrt (T.normalizedAbs (a : F.Carrier)) *
        Real.sqrt (T.normalizedAbs (a : F.Carrier))) *
        ((μ (T.Integers : Set F.Carrier)).toReal *
          (μ (T.Integers : Set F.Carrier)).toReal) := by ring
    _ = T.normalizedAbs (a : F.Carrier) *
        (T.residueCardinality : ℝ) ^ (-T.additiveConductor ψ) := by
      rw [Real.mul_self_sqrt (T.normalizedAbs_nonneg _), hm]
    _ = _ := by
      rw [T.normalizedAbs_of_ne_zero a.ne_zero,
        ← zpow_add₀ (normalization_card_pos T).ne']
      congr 1
      omega

end SuppliedTopology

/-- The exact normalization proposition for every supplied p-adic topology. -/
theorem padicFourierNormalization : PadicFourierNormalizationStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.secondCountableTopology
  intro ψ hψ hne
  dsimp only
  intro n hn
  let χ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier := ⟨ψ, hψ, hne⟩
  have hn' : n = T.additiveConductor χ :=
    hn.unique (T.isGreatest_fractionalIdeal_triviality χ)
  subst n
  have hO : Set.range (fun t : T.Integers => (t : F.Carrier)) =
      (T.Integers : Set F.Carrier) := by
    ext x
    simp
  rw [hO]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ ν hμ hν
    let := hμ
    let := hν
    exact dual_iff_integer_mass T χ μ ν
  · intro μ hμ
    let := hμ
    exact self_dual_iff_integer_mass T χ μ
  · intro μ hμ y
    let := hμ
    exact integer_indicator_fourier_uniformizer T χ μ y
  · intro μ σ hμ hσ hd
    let := hμ
    let := hσ
    exact fixed_haar_ratio T χ μ σ hd
  · intro μ hμ hd a
    let := hμ
    exact self_dual_character_scaling T χ μ hd a

end Langlands.LocalFactors
