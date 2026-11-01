import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport
import Langlands.Representation.GodementJacquet.CentralMatrixRationality
import Langlands.Representation.GodementJacquet.TwoBlockAnalyticReversal
import Langlands.LocalField.Uniformizer

/-! # Common convergence and rationality for supercuspidal matrix coefficients -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

section IotaSupport

variable {F : Type uF} [Field F] {n : ℕ}

/-- Inverse transpose transports a scalar support cover to the image of its
compact representative set. -/
theorem support_coefficientIota_subset_scalarSaturation
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (K : Set (Langlands.GeneralLinear (n + 1) F))
    (hf : Function.support f ⊆ scalarSaturation K) :
    Function.support (coefficientIota f) ⊆
      scalarSaturation (GeneralLinear.inverseTranspose (n + 1) F '' K) := by
  intro g hg
  obtain ⟨a, k, hk, he⟩ := hf hg
  refine ⟨a⁻¹, GeneralLinear.inverseTranspose (n + 1) F k, ⟨k, hk, rfl⟩, ?_⟩
  simpa only [GeneralLinear.inverseTranspose_involutive, map_mul,
    GeneralLinear.inverseTranspose_scalar] using
    congrArg (GeneralLinear.inverseTranspose (n + 1) F) he

end IotaSupport

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance supercuspidalMatrixRationalityTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance supercuspidalMatrixRationalityValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance supercuspidalMatrixRationalityLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance supercuspidalMatrixRationalityT2Space : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance supercuspidalMatrixRationalityMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance supercuspidalMatrixRationalityBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

/-- The scalar matrix of the specified uniformizer, with its centrality proof. -/
def matrixUniformizer (n : ℕ) :
    Subgroup.center (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  GeneralLinear.scalarToCenter
    (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)

theorem matrixUniformizer_det_abs_lt_one (n : ℕ) :
    normalizedAbsoluteValue F.canonicalTopologicalData
      (Matrix.det (matrixUniformizer F n).val.val) < 1 := by
  have hd : Matrix.det (matrixUniformizer F n).val.val =
      ((LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData :
        F.Carrierˣ) : F.Carrier) ^ (n + 1) := by
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar
      (Fin (n + 1)) (LocalFactor.PadicAbelian.uniformizerUnit
        F.canonicalTopologicalData))) : F.Carrier) = _
    simp
  rw [hd, map_pow, normalizedAbsoluteValue_apply,
    LocalFactor.PadicAbelian.uniformizerUnit_coe,
    F.canonicalTopologicalData.normalizedAbs_uniformizer, zpow_neg_one]
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  exact pow_lt_one₀ (inv_nonneg.mpr (by positivity))
    ((inv_lt_one₀ (by positivity)).mpr hq) (Nat.succ_ne_zero n)

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Common convergence and actual rational values with one geometric
denominator for each of the two coefficient families. -/
def SupercuspidalMatrixRationalityData
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ω : ℂˣ) : Prop :=
  MatrixConvergesOnRight F ρ ∧ IotaMatrixConvergesOnRight F ρ ∧
    (∀ Φ : MatrixTestFunction n F.Carrier, ∀ f : biSmoothMatrixCoefficients ρ,
      ∃ R : RationalFunctions,
        HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (generalLinearHaar F.Carrier n) Φ f.val R ∧
        ∃ A : LaurentCoefficients, laurentToRatFunc A =
          laurentToRatFunc (matrixGeometricDenominator F (matrixUniformizer F n).val ω) * R) ∧
    (∀ Φ : MatrixTestFunction n F.Carrier, ∀ f : biSmoothMatrixCoefficients ρ,
      ∃ R : RationalFunctions,
        HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (generalLinearHaar F.Carrier n) Φ (coefficientIota f.val) R ∧
        ∃ A : LaurentCoefficients, laurentToRatFunc A =
          laurentToRatFunc
            (matrixGeometricDenominator F (matrixUniformizer F n).val (ω⁻¹ : ℂˣ)) * R)

/-- The compact scalar-support and Schur consequences of actual
supercuspidality imply both canonical common half-planes and rational families. -/
theorem exists_supercuspidalMatrixRationalityData
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible) :
    ∃ ω : ℂˣ, SupercuspidalMatrixRationalityData F ρ ω := by
  obtain ⟨χ, _, hf⟩ :=
    exists_centralCharacter_compactScalarSupport F.canonicalTopologicalData ρ hρ hi
  let z := matrixUniformizer F n
  let ω := χ z
  have hz := matrixUniformizer_det_abs_lt_one F n
  have hzi : GeneralLinear.inverseTranspose (n + 1) F.Carrier z.val = (z⁻¹).val := by
    change GeneralLinear.inverseTranspose (n + 1) F.Carrier
      (GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit
        F.canonicalTopologicalData)) =
      (GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit
        F.canonicalTopologicalData))⁻¹
    rw [GeneralLinear.inverseTranspose_scalar, map_inv]
  have hcov (f : biSmoothMatrixCoefficients ρ) (g) :
      f.val (z.val * g) = (ω : ℂ) * f.val g :=
    (hf f).2.1 z g
  have hcovI (f : biSmoothMatrixCoefficients ρ) (g) :
      coefficientIota f.val (z.val * g) =
        ((ω⁻¹ : ℂˣ) : ℂ) * coefficientIota f.val g := by
    change f.val (GeneralLinear.inverseTranspose (n + 1) F.Carrier (z.val * g)) = _
    rw [map_mul, hzi]
    simpa only [map_inv, ω, coefficientIota] using
      (hf f).2.1 z⁻¹ (GeneralLinear.inverseTranspose (n + 1) F.Carrier g)
  have hI (f : biSmoothMatrixCoefficients ρ) :
      Continuous (coefficientIota f.val) ∧
        ∃ K : Set (Langlands.GeneralLinear (n + 1) F.Carrier),
          IsCompact K ∧ Function.support (coefficientIota f.val) ⊆ scalarSaturation K := by
    obtain ⟨K, hK, hs⟩ := (hf f).2.2
    exact ⟨(hf f).1.comp (GeneralLinear.continuous_inverseTranspose _ _),
      _, hK.image (GeneralLinear.continuous_inverseTranspose _ _),
      support_coefficientIota_subset_scalarSaturation f.val K hs⟩
  obtain ⟨a, ha⟩ := exists_halfPlane_norm_matrixRatio_lt_one
    (normalizedAbsoluteValue F.canonicalTopologicalData) z.val hz (ω : ℂ) (jpssShift n)
  obtain ⟨aI, haI⟩ := exists_halfPlane_norm_matrixRatio_lt_one
    (normalizedAbsoluteValue F.canonicalTopologicalData) z.val hz
    ((ω⁻¹ : ℂˣ) : ℂ) (jpssShift n)
  refine ⟨ω, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine ⟨a, fun Φ f s hs => ?_⟩
    obtain ⟨K, hK, hS⟩ := (hf f).2.2
    obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_quotient
      F z.val hz ω Φ f.val (hf f).1 (hcov f) K hK hS
    exact (hA s (ha s hs)).1
  · refine ⟨aI, fun Φ f s hs => ?_⟩
    obtain ⟨K, hK, hS⟩ := (hI f).2
    obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_quotient
      F z.val hz (ω⁻¹ : ℂˣ) Φ (coefficientIota f.val) (hI f).1 (hcovI f) K hK hS
    exact (hA s (haI s hs)).1
  · intro Φ f
    obtain ⟨K, hK, hS⟩ := (hf f).2.2
    exact exists_shiftedRationalValue_of_scalarSaturation
      F z.val hz ω Φ f.val (hf f).1 (hcov f) K hK hS
  · intro Φ f
    obtain ⟨K, hK, hS⟩ := (hI f).2
    exact exists_shiftedRationalValue_of_scalarSaturation
      F z.val hz (ω⁻¹ : ℂˣ) Φ (coefficientIota f.val) (hI f).1 (hcovI f) K hK hS

end Padic

end Langlands.GodementJacquet
