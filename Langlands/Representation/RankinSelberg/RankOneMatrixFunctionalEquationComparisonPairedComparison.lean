import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonComplementaryContinuation
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly

/-! # Assembly from a concrete same-coefficient paired matrix comparison

The actual matrix premise and proved block continuations remove all analytic
inputs from the assembly boundary. What remains is the simultaneous original
and genuine-dual comparison with one actual coefficient and one nonzero scalar.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-- A common nonzero scalar cancels from a normalized equation, while retaining
the full reduced-denominator domain of both unscaled rational functions. -/
theorem NormalizedFunctionalEquation.of_const_mul
    {q : ℕ} {P PDual : Polynomial ℂ} {ζ c : ℂˣ} {e : ℕ} {m : ℤ}
    {R Rd : RationalFunctions} (t : ℂ) (ht : t ≠ 0)
    (h : NormalizedFunctionalEquation q P PDual ζ c e m
      (RatFunc.C t * R) (RatFunc.C t * Rd)) :
    NormalizedFunctionalEquation q P PDual ζ c e m R Rd := by
  intro s hR hRd
  have hc (z : ℂ) : RationalEvaluation.RegularAt (RatFunc.C t) z := by
    simpa using (RationalEvaluation.RegularAt.polynomial (z := z) (Polynomial.C t))
  have he := h s ((hc _).mul hR) ((hc _).mul hRd)
  rw [RationalEvaluation.eval_mul (hc _) hR, RationalEvaluation.eval_mul (hc _) hRd,
    RatFunc.eval_C, RatFunc.eval_C] at he
  simp only [RingHom.id_apply] at he
  apply mul_left_cancel₀ ht
  calc
    t * (PDual.eval (spectralPoint q (1 - s)) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd) =
      PDual.eval (spectralPoint q (1 - s)) *
        (t * RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd) := by ring
    _ = _ := he
    _ = _ := by ring

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance pairedComparisonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance pairedComparisonValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance pairedComparisonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance pairedComparisonScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance pairedComparisonScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance pairedComparisonT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance pairedComparisonTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance pairedComparisonGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance pairedComparisonGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance pairedComparisonUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance pairedComparisonUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance pairedComparisonQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance pairedComparisonQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ)

/-- The concrete paired extraction boundary: one actual original coefficient,
one test and one common nonzero scalar compare to the literal original and
genuine complementary-dual block-zero integrals on right half-planes. -/
def PairedMatrixBlockComparison (hrpos : 0 < r) : Prop :=
  ∀ w : (glCoefficientModel ψ r σ ℓ).toSubmodule,
    ∃ Φ : GodementJacquet.MatrixTestFunction r F.Carrier,
      ∃ f : GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
      ∃ C : ℂ, C ≠ 0 ∧
        (∃ b : ℝ, ∀ s : ℂ, b < s.re →
          GodementJacquet.matrixIntegral (normalizedAbsoluteValue F.canonicalTopologicalData)
              (generalLinearHaar F.Carrier r) Φ (s + GodementJacquet.jpssShift r) f.val =
            C * unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ
              (normalizedAbsoluteValue F.canonicalTopologicalData)
              (unipotentQuotientHaar F.Carrier 0) (rectangularMeasure ν 0 (0 + 1))
              w.val (rankOneTrivialModelOne ψ).val s) ∧
        ∀ ΦHat : GodementJacquet.MatrixTestFunction r F.Carrier,
          GodementJacquet.Padic.MatrixFourierPair F ψ ν Φ ΦHat →
          ∃ b : ℝ, ∀ s : ℂ, b < s.re →
            GodementJacquet.matrixIntegral (normalizedAbsoluteValue F.canonicalTopologicalData)
                (generalLinearHaar F.Carrier r) ΦHat (s + GodementJacquet.jpssShift r)
                (GodementJacquet.coefficientIota f.val) =
              C * dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ
                (normalizedAbsoluteValue F.canonicalTopologicalData)
                (unipotentQuotientHaar F.Carrier 0) ν σ
                (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
                w (rankOneTrivialModelOne ψ) s

/-- The supplied matrix data and the concrete paired comparison suffice for
the full positive-rank gamma conclusion. All analytic premises are derived. -/
theorem rankOneGammaFactor_of_pairedMatrixComparison (hrpos : 0 < r)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (hν : IsSelfDual ψ ν) (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hData : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ) P PDual c a)
    (hComparison : PairedMatrixBlockComparison F ψ ν σ ℓ hrpos) :
    IsPadicSymmetricGammaFactor F ψ ν σ (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual) := by
  have hPDual : PDual ≠ 0 := hData.2.1.2.2.polynomial_ne_zero
  apply rankOneGammaFactor_of_normalized_blockZero_one F ψ ν σ hσ ℓ hℓ hrpos hν hPDual
  intro w
  obtain ⟨R, hR⟩ := RankOneBlockReduction.rationalContinuation_of_matrix F ψ ν σ ℓ
    (unipotentQuotientHaar F.Carrier 0) hrpos hσ hℓ
    (unipotentQuotientHaar_isCompatible F.Carrier 0) P hData.1 0 (r - 0 - 1) (by omega) w
  obtain ⟨Rd, hRd⟩ := RankOneBlockReduction.dualBlockZero_rationalContinuation_of_iota
    F ψ ν σ ℓ (unipotentQuotientHaar F.Carrier 0) hrpos hσ hℓ
    (unipotentQuotientHaar_isCompatible F.Carrier 0) PDual hData.2.1 w
  obtain ⟨Φ, f, C, hC, he, hed⟩ := hComparison w
  obtain ⟨ΦHat, hpair, hFE⟩ := hData.2.2 Φ
  obtain ⟨RM, hRM⟩ := hData.1.2.1 Φ f
  obtain ⟨RMd, hRMd⟩ := hData.2.1.2.1 ΦHat f
  have hEqR : RM = RatFunc.C C * R := hRM.2.unique
    F.canonicalTopologicalData.residueCardinality_gt_one
    (RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul C hR) he)
  have hEqRd : RMd = RatFunc.C C * Rd := hRMd.2.unique
    F.canonicalTopologicalData.residueCardinality_gt_one
    (RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul C hRd) (hed ΦHat hpair))
  have hN := hFE f RM RMd hRM hRMd
  rw [hEqR, hEqRd] at hN
  exact ⟨R, Rd, hR, hRd, hN.of_const_mul C hC⟩

end Padic

end Langlands.RankinSelberg
