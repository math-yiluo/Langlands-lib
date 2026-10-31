import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxConvergence
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonLeft

/-! # The actual original block-zero integral from matrix analytic data

The canonical second vector and actual rank-one quotient measure identify the
literal block-zero integral with the original rank-one model integral.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section Transport

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]

omit [IsTopologicalRing F] in
/-- The literal equality wrapper transports only the first Whittaker function. -/
theorem unequalRankIntegralAt_eq_rankCast (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ n) :
    unequalRankIntegralAt j k hr ψ abv μ ρ W W' =
      unequalRankIntegral ψ abv j k μ ρ
        (InducedTailIntermediate.whittakerRankCast ψ hr W) W' := by
  subst r
  rfl

end Transport

section Original

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [MeasurableSpace (Langlands.GeneralLinear (0 + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (0 + 1) F)]
  [MeasurableSpace (upperUnipotent (0 + 1) F)] [BorelSpace (upperUnipotent (0 + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F)
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
  (ℓ : glFunctionals ψ (m + 1) σ)
  (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
  (μ : Measure (LeftUnipotentQuotient 0 F))
  (hμ : IsCompatible (upperUnipotent (0 + 1) F) (generalLinearHaar F 0)
    (unipotentHaar F 0) μ)

include hμ in
/-- With the canonical actual second vector, the literal block-zero quotient
integral equals the rank-one model integral for every compatible quotient measure. -/
theorem unequalRankIntegralAt_rankOne_one (k : ℕ) (hr : m + 1 = 0 + (0 + k + 1)) :
    unequalRankIntegralAt 0 k hr ψ abv μ (rectangularMeasure ν 0 (0 + 1))
        w.val (rankOneTrivialModelOne ψ).val =
      fun s => ∫ g, rankOneModelIntegrand ψ abv σ ℓ w s g ∂generalLinearHaar F 0 := by
  have hk : k = m := by omega
  subst k
  rw [eq_rankOneQuotientHaar_of_isCompatible F μ hμ,
    unequalRankIntegralAt_eq_rankCast, rectangularMeasure_zero_rows]
  funext s
  rw [unequalRankIntegral]
  simp only [integral_dirac]
  rw [integral_rankOneQuotientHaar]
  apply integral_congr_ae
  filter_upwards [] with g
  simpa only [one_mul, rankOneModelIntegrand, glModelFunction] using
    unequalRankIntegrand_whittakerRankCast ψ abv m (by omega) w.val
      (rankOneTrivialModelOne ψ).val 1 (rankOneTrivialModelOne_apply ψ) s 0 g

include hμ in
/-- Absolute block-zero convergence is exactly original rank-one convergence. -/
theorem unequalRankConverges_rankOne_one_iff (s : ℂ) :
    UnequalRankConverges ψ abv 0 m μ (rectangularMeasure ν 0 (0 + 1))
        (InducedTailIntermediate.whittakerRankCast ψ (by omega) w.val)
        (rankOneTrivialModelOne ψ).val s ↔
      Integrable (rankOneModelIntegrand ψ abv σ ℓ w s) (generalLinearHaar F 0) := by
  rw [eq_rankOneQuotientHaar_of_isCompatible F μ hμ, UnequalRankConverges,
    rectangularMeasure_zero_rows]
  let _ : Unique (Matrix (Fin 0) (Fin (0 + 1)) F) := Pi.uniqueOfIsEmpty _
  rw [integrable_prod_dirac_iff]
  refine (integrable_map_equiv rankOneQuotientHomeomorph.symm.toMeasurableEquiv _).trans ?_
  apply integrable_congr
  filter_upwards [] with g
  change unequalRankIntegrand ψ abv 0 m
    (InducedTailIntermediate.whittakerRankCast ψ (by omega) w.val)
      (rankOneTrivialModelOne ψ).val s 0 (Quotient.mk _ g) = _
  simpa only [one_mul, rankOneModelIntegrand, glModelFunction] using
    unequalRankIntegrand_whittakerRankCast ψ abv m (by omega) w.val
      (rankOneTrivialModelOne ψ).val 1 (rankOneTrivialModelOne_apply ψ) s 0 g

end Original

namespace PadicOriginalBlockZero

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance originalBlockZeroTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance originalBlockZeroValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance originalBlockZeroLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance originalBlockZeroScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance originalBlockZeroScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance originalBlockZeroGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance originalBlockZeroGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance originalBlockZeroUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance originalBlockZeroUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance originalBlockZeroQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance originalBlockZeroQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
  (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
  (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
    (unipotentHaar F.Carrier 0) μ)

/-- Actual original block-zero analytics for the canonical second vector:
a common convergence half-plane and a continuation for each first model vector. -/
def AnalyticAssertions : Prop :=
  (∃ b : ℝ, ∀ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
    ∀ s : ℂ, b < s.re →
      UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        0 m μ (rectangularMeasure ν 0 (0 + 1))
        (InducedTailIntermediate.whittakerRankCast ψ (by omega) w.val)
        (rankOneTrivialModelOne ψ).val s) ∧
  ∀ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
    ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (unequalRankIntegralAt 0 ((m + 1) - 0 - 1) (by omega) ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μ
          (rectangularMeasure ν 0 (0 + 1)) w.val (rankOneTrivialModelOne ψ).val) R

include hσ hμ in
/-- The supplied original matrix half-plane is also a common actual block-zero
half-plane for every first model vector and the canonical second vector. -/
theorem convergesOnRight_of_matrix
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    ∃ b : ℝ, ∀ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
        UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          0 m μ (rectangularMeasure ν 0 (0 + 1))
          (InducedTailIntermediate.whittakerRankCast ψ (by omega) w.val)
          (rankOneTrivialModelOne ψ).val s := by
  obtain ⟨b, hb⟩ := RankOneBox.rankOneModel_convergesOnRight_of_matrix F ψ σ ℓ hσ hMatrix
  refine ⟨b, fun w s hs => ?_⟩
  exact (unequalRankConverges_rankOne_one_iff ψ _ ν σ ℓ w μ hμ s).mpr (hb w s hs)

include hσ hμ in
/-- Matrix analytic assertions give a rational continuation of the literal
original block-zero integral, without an additional rank-one analytic premise. -/
theorem rationalContinuation_of_matrix (P : Polynomial ℂ)
    (hMatrix : GodementJacquet.Padic.MatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P)
    (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) :
    ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (unequalRankIntegralAt 0 ((m + 1) - 0 - 1) (by omega) ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μ
          (rectangularMeasure ν 0 (0 + 1)) w.val (rankOneTrivialModelOne ψ).val) R := by
  obtain ⟨R, -, hR⟩ := RankOneBox.rankOneModel_rationalContinuation_of_matrix
    F ψ σ ℓ w hσ P hMatrix
  refine ⟨R, ?_⟩
  rw [unequalRankIntegralAt_rankOne_one ψ _ ν σ ℓ w μ hμ]
  exact hR

include hσ hμ in
/-- All original block-zero analytic assertions follow from the actual
coefficient-model matrix analytic assertions. -/
theorem analyticAssertions_of_matrix (P : Polynomial ℂ)
    (hMatrix : GodementJacquet.Padic.MatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P) :
    AnalyticAssertions F ψ ν σ ℓ μ :=
  ⟨convergesOnRight_of_matrix F ψ ν σ hσ ℓ μ hμ hMatrix.1,
    rationalContinuation_of_matrix F ψ ν σ hσ ℓ μ hμ P hMatrix⟩

end PadicOriginalBlockZero

end Langlands.RankinSelberg
