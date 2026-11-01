import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
import Langlands.Representation.GodementJacquet.RegularMatrixZetaOperator

/-! Cancellation of the determinant density on regular matrix functions. -/

noncomputable section

namespace Langlands.RankinSelberg.GLDeterminantDensity

open MeasureTheory
open scoped NNReal

universe uK

variable {K : Type uK} [Field K]

/-- The positive determinant power cancelling the GL density. -/
abbrev matrixDeterminantPower (r : ℕ) (χ : K →*₀ ℝ≥0)
    (X : Matrix (Fin r) (Fin r) K) : ℝ≥0 :=
  forwardWeight r χ X

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
  (r : ℕ) (χ : K →*₀ ℝ≥0)
  [MeasurableSpace (Matrix (Fin r) (Fin r) K)]
  [BorelSpace (Matrix (Fin r) (Fin r) K)]
  [MeasurableSpace (GeneralLinear r K)] [BorelSpace (GeneralLinear r K)]

/-- If a function vanishes on the singular locus, multiplying its group
restriction by the positive determinant power cancels the exact density. -/
theorem integral_matrixDeterminantPower
    (hχ : Continuous χ) (μ : Measure (Matrix (Fin r) (Fin r) K))
    (f : Matrix (Fin r) (Fin r) K → ℂ)
    (hf : ∀ X, ¬ IsUnit X → f X = 0) :
    (∫ g : GeneralLinear r K,
      (matrixDeterminantPower r χ g.val : ℂ) * f g.val
        ∂weightedRestriction r χ μ) = ∫ X, f X ∂μ := by
  rw [integral_weightedRestriction r χ hχ μ
    (fun X => (matrixDeterminantPower r χ X : ℂ) * f X)]
  calc
    _ = ∫ X in Set.range (Units.val : GeneralLinear r K →
        Matrix (Fin r) (Fin r) K), f X ∂μ := by
      apply setIntegral_congr_fun
        (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range.measurableSet
      rintro X ⟨g, rfl⟩
      have hg : χ g.val.det ≠ 0 :=
        (g.isUnit.map (MonoidHomClass.toMonoidHom χ |>.comp
          (Matrix.detMonoidHom : Matrix (Fin r) (Fin r) K →* K))).ne_zero
      simp only [matrixWeight, matrixDeterminantPower, forwardWeight, NNReal.smul_def,
        Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
        ← NNReal.coe_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hg),
        NNReal.coe_one, Complex.ofReal_one, one_mul]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro X hX
      apply hf X
      rintro ⟨g, rfl⟩
      exact hX ⟨g, rfl⟩

end Langlands.RankinSelberg.GLDeterminantDensity

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg
open scoped NNReal

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance regularDensityTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance regularDensityValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance regularDensityLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance regularDensityT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance regularDensitySecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance regularDensityMeasurable : MeasurableSpace F.Carrier := borel _
local instance regularDensityBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance regularDensityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance regularDensityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

/-- A single positive scalar compares all regular matrix functions, with
the determinant density cancelled by the actual integer zeta weight. -/
theorem exists_integral_regularMatrix_density (n : ℕ)
    (ν : AdditiveHaarMeasure F.Carrier) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (f : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ),
        (∀ X, ¬ IsUnit X → f X = 0) →
        (c : ℂ) * (∫ g : GeneralLinear (n + 1) F.Carrier,
          f g.val *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              g ((n + 1 : ℕ) : ℂ) ∂generalLinearHaar F.Carrier n) =
          ∫ X, f X ∂rectangularMeasure ν (n + 1) (n + 1) := by
  obtain ⟨c, hc, hμ⟩ :=
    GLDeterminantDensity.padic_exists_weightedRestriction_eq_generalLinearHaar
      F F.canonicalTopologicalData n (rectangularMeasure ν (n + 1) (n + 1))
  refine ⟨c, hc, ?_⟩
  intro f hf
  have h := GLDeterminantDensity.integral_matrixDeterminantPower
    (n + 1) F.canonicalTopologicalData.normalizedAbsHom
    F.canonicalTopologicalData.continuous_normalizedAbsHom
    (rectangularMeasure ν (n + 1) (n + 1)) f hf
  rw [hμ, integral_smul_nnreal_measure] at h
  have hw (g : GeneralLinear (n + 1) F.Carrier) :
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        g ((n + 1 : ℕ) : ℂ) =
      (GLDeterminantDensity.matrixDeterminantPower (n + 1)
        F.canonicalTopologicalData.normalizedAbsHom g.val : ℂ) := by
    change (F.canonicalTopologicalData.normalizedAbs g.val.det : ℂ) ^
      ((n + 1 : ℕ) : ℂ) = _
    simp only [Complex.cpow_natCast,
      GLDeterminantDensity.matrixDeterminantPower, GLDeterminantDensity.forwardWeight, NNReal.coe_pow,
      Complex.ofReal_pow, PadicField.TopologicalData.normalizedAbsHom_coe]
  simp_rw [hw]
  simpa only [NNReal.smul_def, Complex.real_smul, mul_comm] using h

end Langlands.GodementJacquet.Padic
