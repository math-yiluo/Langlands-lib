import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport

/-! # Unitary left translation and the complex square Fourier integral -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open scoped NNReal ENNReal Langlands.Archimedean.ComplexDuality

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

variable {n : ℕ}

local notation "Kc" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "ι" => GeneralLinear.inverseTranspose n ℂ

local instance : LocallyCompactSpace Mat :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

private def leftMul (k : Kc) (X : Mat) : Mat := k.val.val * X

private theorem leftMul_mul (k j : Kc) (X : Mat) :
    leftMul (k * j) X = leftMul k (leftMul j X) := Matrix.mul_assoc _ _ _

private theorem leftMul_one (X : Mat) : leftMul 1 X = X := Matrix.one_mul _

private def leftMulAddEquiv (k : Kc) : Mat ≃+ Mat where
  toFun := leftMul k
  invFun := leftMul k⁻¹
  left_inv X := by rw [← leftMul_mul, inv_mul_cancel, leftMul_one]
  right_inv X := by rw [← leftMul_mul, mul_inv_cancel, leftMul_one]
  map_add' X Y := Matrix.mul_add _ _ _

private theorem continuous_leftMul (k : Kc) : Continuous (leftMul k) :=
  continuous_const.matrix_mul continuous_id

/-- Left multiplication by a unitary matrix preserves every additive Haar
measure on the square matrix space. -/
theorem measurePreserving_complexUnitaryMatrixLeft (μ : Measure Mat) [μ.IsAddHaarMeasure]
    (k : Kc) : MeasurePreserving (fun X : Mat => k.val.val * X) μ μ := by
  let e := leftMulAddEquiv k
  have he : Continuous e := continuous_leftMul k
  let : (μ.map e).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map μ he (continuous_leftMul k⁻¹)
  obtain ⟨S, hSc, hS⟩ := exists_compact_mem_nhds (0 : Mat)
  let f (p : Kc × Mat) := leftMul p.1 p.2
  let C := f '' (Set.univ ×ˢ S)
  have hf : Continuous f :=
    ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_mul continuous_snd
  have hC : IsCompact C := (isCompact_univ.prod hSc).image hf
  have hSC : S ⊆ C := fun X hX => ⟨(1, X), ⟨Set.mem_univ _, hX⟩, leftMul_one X⟩
  have hpre : e ⁻¹' C = C := by
    ext X
    change leftMul k X ∈ C ↔ X ∈ C
    constructor
    · rintro ⟨⟨j, Y⟩, ⟨_, hY⟩, hE⟩
      change leftMul j Y = leftMul k X at hE
      refine ⟨(k⁻¹ * j, Y), ⟨Set.mem_univ _, hY⟩, ?_⟩
      change leftMul (k⁻¹ * j) Y = X
      rw [leftMul_mul, hE, ← leftMul_mul, inv_mul_cancel, leftMul_one]
    · rintro ⟨⟨j, Y⟩, ⟨_, hY⟩, hE⟩
      change leftMul j Y = X at hE
      refine ⟨(k * j, Y), ⟨Set.mem_univ _, hY⟩, ?_⟩
      change leftMul (k * j) Y = leftMul k X
      rw [leftMul_mul, hE]
  have hmap : (μ.map e) C = μ C := by
    rw [Measure.map_apply he.measurable hC.measurableSet, hpre]
  have hscale := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ
  have hCpos := Measure.measure_pos_of_mem_nhds μ (Filter.mem_of_superset hS hSC)
  have hc : (Measure.addHaarScalarFactor (μ.map e) μ : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj hCpos.ne' hC.measure_lt_top.ne).mp
    have h := congrArg (fun ν : Measure Mat => ν C) hscale
    change μ.map e C = (Measure.addHaarScalarFactor (μ.map e) μ : ℝ≥0∞) * μ C at h
    rw [hmap] at h
    simpa only [one_mul] using h.symm
  refine ⟨he.measurable, ?_⟩
  change μ.map e = μ
  rw [hscale, ENNReal.coe_eq_one.mp hc, one_smul]

/-- The square Fourier integral carries unitary left translation to left
translation by the inverse transpose, with no measure multiplier. -/
def ComplexLocalUnitaryMatrixFourierStatement (n : ℕ) : Prop :=
  ∀ (a : ℂˣ) (k : unitaryCompact ℂ n)
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
    rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
      (fun Y => Φ (k.val.val * Y)) X =
    rectangularFourierIntegral (complexScaledCharacter a) (complexSelfDualMeasure a)
      Φ ((GeneralLinear.inverseTranspose n ℂ k.val).val * X)

theorem complexLocalUnitaryMatrixFourier : ComplexLocalUnitaryMatrixFourierStatement n := by
  intro a k Φ X
  let ν := complexSelfDualMeasure a
  let μ := RankinSelberg.rectangularMeasure ν n n
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let : μ.IsAddHaarMeasure := RankinSelberg.rectangularMeasure_isAddHaar ν n n
  have hmap : μ.map (rectangularLeftRightHomeomorph k.val (1 : G)) = (1 : ℝ≥0) • μ := by
    rw [one_smul]
    change μ.map (fun Y : Mat => k.val.val * Y * 1) = μ
    simpa only [Matrix.mul_one] using (measurePreserving_complexUnitaryMatrixLeft μ k).map_eq
  simpa only [Units.val_one, Matrix.mul_one, map_one, NNReal.coe_one, Complex.ofReal_one, one_mul]
    using rectangularFourierIntegral_leftRight (complexScaledCharacter a) ν k.val 1 1 hmap Φ X

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
