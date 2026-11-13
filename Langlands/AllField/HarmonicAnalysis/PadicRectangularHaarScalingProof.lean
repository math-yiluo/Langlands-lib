import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
noncomputable section

open Set MeasureTheory MeasureTheory.Measure Matrix
open scoped NNReal ENNReal Kronecker

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

section Product
variable {K ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [Fintype ι] [DecidableEq ι]
  (ν : Measure K) [SigmaFinite ν] [IsAddLeftInvariant ν]

variable (χ : K →*₀ ℝ≥0)
  (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)

include hχ

end Product

section Haar
variable {K ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K]
  [Fintype ι] [DecidableEq ι]
  (ν : Measure K) [IsAddHaarMeasure ν]
  (χ : K →*₀ ℝ≥0)
  (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)

include hχ

end Haar

section Rectangular
variable {K m n : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end Rectangular

universe uF

/-- Left and inverse-right multiplication scale every rectangular additive Haar
measure by the inverse residue-normalized determinant quotient. -/
theorem padicRectangularHaarScaling (F : Type uF) [Field F]
    (T : LocalFieldData F) (r s : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F)]
      [BorelSpace (Matrix (Fin r) (Fin s) F)]
      (μ : Measure (Matrix (Fin r) (Fin s) F)) [IsAddHaarMeasure μ]
      (A : GeneralLinear r F) (B : GeneralLinear s F),
      μ.map (fun X => (A : Matrix (Fin r) (Fin r) F) * X *
        ((B⁻¹ : GeneralLinear s F) : Matrix (Fin s) (Fin s) F)) =
        (((T.determinantNorm r A : ℝ≥0) ^ s /
          (T.determinantNorm s B : ℝ≥0) ^ r)⁻¹) • μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro _ _ μ _ A B
  have hχ (a : F) (ha : a ≠ 0) :
      (addHaar : Measure F).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • addHaar :=
    padicScalarHaarScaling F T addHaar (Units.mk0 a ha)
  have h := haarMeasure_map_rectangular addHaar T.normalizedAbsHom hχ μ
    (A : Matrix (Fin r) (Fin r) F)
    ((B⁻¹ : GeneralLinear s F) : Matrix (Fin s) (Fin s) F)
    (GeneralLinear.determinant A).ne_zero (GeneralLinear.determinant B⁻¹).ne_zero
  change μ.map _ =
    ((T.determinantNorm r A : ℝ≥0) ^ Fintype.card (Fin s) *
      (T.determinantNorm s B⁻¹ : ℝ≥0) ^ Fintype.card (Fin r))⁻¹ • μ at h
  simpa only [Fintype.card_fin, map_inv, Units.val_inv_eq_inv_val,
    inv_pow, div_eq_mul_inv] using h

/-- The exact published rectangular Haar scaling proposition. -/
theorem padicRectangularHaarScalingStatement : PadicRectangularHaarScalingStatement.{uF} := by
  intro F _ T r s
  exact padicRectangularHaarScaling F T r s

end Langlands.AllField.HarmonicAnalysis
