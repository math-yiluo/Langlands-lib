import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxConvergence
import Langlands.Representation.GodementJacquet.CoefficientTransport
import Langlands.Representation.RankinSelberg.DualModels

/-! # Actual first-dual rank-one convergence from inverse-transpose matrix data

The first dual coefficient model is equivalent to the inverse-transpose pullback
of the original model. Its ordinary matrix analytics and rank-one convergence
therefore follow from the supplied transformed matrix analytic assertions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

section ModelTransport

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (ℓ : glFunctionals ψ n σ)

/-- The actual first dual map intertwines the original model's inverse-transpose
pullback with the actual standard model for the reversed additive character. -/
def firstDualModelRepresentationEquiv :
    (inverseTransposePullback (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ)).Equiv
      (glModelRepresentation (ψ.scale (-1)) n (inverseTransposePullback σ)
        (firstDualFunctional ψ σ ℓ)) :=
  Representation.Equiv.mk (firstDualModelEquiv ψ σ ℓ) (fun s => by
    ext f g
    change f.val.val ((weylLong (n + 1) F * inverseTranspose (n + 1) F g) *
        inverseTranspose (n + 1) F s) =
      f.val.val (weylLong (n + 1) F * inverseTranspose (n + 1) F (g * s))
    rw [map_mul, mul_assoc])

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]

/-- The same measure, polynomial, shifted half-plane and actual value family
transfer from transformed original coefficients to the first dual model. -/
theorem iotaMatrixAnalyticAssertions_firstDual_iff
    (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F)) (P : Polynomial ℂ) :
    GodementJacquet.IotaMatrixAnalyticAssertions q abv μ
        (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
        (glModelRepresentation ψ n σ ℓ) P ↔
      GodementJacquet.MatrixAnalyticAssertions q abv μ
        (V := (glCoefficientModel (ψ.scale (-1)) n (inverseTransposePullback σ)
          (firstDualFunctional ψ σ ℓ)).toSubmodule)
        (glModelRepresentation (ψ.scale (-1)) n (inverseTransposePullback σ)
          (firstDualFunctional ψ σ ℓ)) P :=
  (GodementJacquet.iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose q abv μ P).trans
    (GodementJacquet.matrixAnalyticAssertions_equiv q abv μ
      (firstDualModelRepresentationEquiv ψ σ ℓ) P)

end ModelTransport

namespace PadicFirstDual

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance firstDualConvergenceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance firstDualConvergenceValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance firstDualConvergenceLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance firstDualConvergenceGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance firstDualConvergenceGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)

/-- The inverse-transpose matrix assertions give ordinary matrix assertions
of the actual first dual coefficient model, with the same polynomial. -/
theorem matrixAnalyticAssertions_of_iota (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P) :
    GodementJacquet.Padic.MatrixAnalyticAssertions F
      (V := (glCoefficientModel (ψ.scale (-1)) (m + 1) (inverseTransposePullback σ)
        (firstDualFunctional ψ σ ℓ)).toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) (m + 1) (inverseTransposePullback σ)
        (firstDualFunctional ψ σ ℓ)) P :=
  (iotaMatrixAnalyticAssertions_firstDual_iff ψ σ ℓ
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier (m + 1)) P).mp hIota

include hσ in
/-- One right half-plane works for the actual first dual functions of every
original model vector, including every supplied right translate. -/
theorem rankOne_convergesOnRight_of_iota (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P) :
    ∃ b : ℝ, ∀ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ a : Langlands.GeneralLinear (m + 1 + 1) F.Carrier,
        ∀ s : ℂ, b < s.re → Integrable
          (fun g => (firstDualFunction ψ (m + 1) w.val).val (rankOneEmbedding m g * a) *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
              (s - ((m + 1 : ℕ) : ℂ) / 2))
          (generalLinearHaar F.Carrier 0) := by
  have hMd := matrixAnalyticAssertions_of_iota F ψ σ ℓ P hIota
  obtain ⟨b, hb⟩ := RankOneBox.rankOneModel_convergesOnRight_of_matrix F (ψ.scale (-1))
    (inverseTransposePullback σ) (firstDualFunctional ψ σ ℓ)
    (inverseTransposePullback_isSmooth σ hσ) hMd.1
  refine ⟨b, fun w a s hs => ?_⟩
  exact hb (translatedFirstDualModelEquiv ψ σ ℓ a w) s hs

include hσ in
/-- Each actual first dual function and right translate also has a rational
continuation of its rank-one integral, supplied by the transformed matrix data. -/
theorem rankOne_rationalContinuation_of_iota (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P)
    (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (a : Langlands.GeneralLinear (m + 1 + 1) F.Carrier) :
    ∃ R : RationalFunctions,
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable
        (fun g => (firstDualFunction ψ (m + 1) w.val).val (rankOneEmbedding m g * a) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
            (s - ((m + 1 : ℕ) : ℂ) / 2)) (generalLinearHaar F.Carrier 0)) ∧
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => ∫ g, (firstDualFunction ψ (m + 1) w.val).val (rankOneEmbedding m g * a) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
            (s - ((m + 1 : ℕ) : ℂ) / 2) ∂generalLinearHaar F.Carrier 0) R := by
  have hMd := matrixAnalyticAssertions_of_iota F ψ σ ℓ P hIota
  exact RankOneBox.rankOneModel_rationalContinuation_of_matrix F (ψ.scale (-1))
    (inverseTransposePullback σ) (firstDualFunctional ψ σ ℓ)
    (translatedFirstDualModelEquiv ψ σ ℓ a w)
    (inverseTransposePullback_isSmooth σ hσ) P hMd

end PadicFirstDual

end Langlands.RankinSelberg
