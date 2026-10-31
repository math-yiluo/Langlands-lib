import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonOriginalBlockZero
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonDualConvergence
import Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof

/-! # Actual complementary-block continuations from transformed matrix data

Compact rectangular support reduces each scalar block integral to a block-zero
integral of one vector in the same coefficient model. This transfers the already
proved rank-one continuations, including to the literal genuine dual integral.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

namespace RankOneBlockReduction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance blockReductionTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance blockReductionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance blockReductionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance blockReductionT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance blockReductionSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance blockReductionScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance blockReductionScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance blockReductionGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance blockReductionGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance blockReductionUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance blockReductionUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance blockReductionQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance blockReductionQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ)
  (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))

/-- All actual scalar blocks can be reduced to zero rectangular rows using
one coefficient vector, uniformly in the second function and spectral parameter. -/
def BlockZeroReduction : Prop :=
  ∀ (j k : ℕ) (hr : r = 0 + (j + k + 1)),
    ∀ f : (coefficientModel σ ℓ).toSubmodule,
      ∃ f₀ : (coefficientModel σ ℓ).toSubmodule,
        ∀ (f' : InverseWhittakerFunctions ψ 0) (s : ℂ),
          unequalRankIntegralAt j k hr ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
              μ (rectangularMeasure ν j (0 + 1)) f.val f' s =
            unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ
              (normalizedAbsoluteValue F.canonicalTopologicalData)
              μ (rectangularMeasure ν 0 (0 + 1)) f₀.val f' s

/-- Published uniform compact support and last-row integration discharge the
scalar reduction property without assuming any quotient convergence. -/
theorem blockZeroReduction
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0) :
    BlockZeroReduction F ψ ν σ ℓ μ := by
  intro j
  induction j with
  | zero =>
      intro k hr f
      have hk : k = r - 0 - 1 := by omega
      subst k
      exact ⟨f, fun _ _ => rfl⟩
  | succ j ih =>
      intro k hr f
      have hs : ∃ C : Set (Matrix (Fin (j + 1)) (Fin (0 + 1)) F.Carrier),
          IsCompact C ∧ ∀ g X,
            f.val.val (AdjacentBlockReduction.blockMatrixAt (j + 1) k hr g X) ≠ 0 → X ∈ C := by
        subst r
        exact unequalRankCompactSupport F F.canonicalTopologicalData 0 (j + 1) k
          ψ V σ hσ ℓ hℓ f
      obtain ⟨C, hC, hs⟩ := hs
      obtain ⟨f₁, hf₁⟩ := AdjacentBlockReduction.exists_adjacent_integral_coefficient ν
        0 r j k hr (by omega) ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        μ σ hσ.1.1 ℓ f C hC hs
      obtain ⟨f₀, hf₀⟩ := ih (k + 1) (by omega) f₁
      exact ⟨f₀, fun f' s => (hf₁ f' s).trans (hf₀ f' s)⟩

/-- Every scalar block of the canonical-vector pair has a rational continuation
from the actual coefficient-model matrix assertions and full Whittaker type. -/
theorem rationalContinuation_of_matrix (hrpos : 0 < r)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
      (unipotentHaar F.Carrier 0) μ)
    (P : Polynomial ℂ)
    (hMatrix : GodementJacquet.Padic.MatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ) P)
    (j k : ℕ) (hr : r = 0 + (j + k + 1))
    (f : (coefficientModel σ ℓ).toSubmodule) :
    ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (unequalRankIntegralAt j k hr ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          μ (rectangularMeasure ν j (0 + 1)) f.val (rankOneTrivialModelOne ψ).val) R := by
  cases r with
  | zero => omega
  | succ m =>
      obtain ⟨f₀, hf₀⟩ := blockZeroReduction F ψ ν σ ℓ μ hσ hℓ j k hr f
      obtain ⟨R, hR⟩ := PadicOriginalBlockZero.rationalContinuation_of_matrix
        F ψ ν σ hσ.1.1 ℓ μ hμ P hMatrix f₀
      exact ⟨R, RationalContinuationLinear.continuation_of_eq_on_right hR
        ⟨0, fun s _ => hf₀ (rankOneTrivialModelOne ψ).val s⟩⟩

/-- The literal genuine dual integral, including its complementary rectangular
block and actual block Weyl translate, has a continuation from the supplied
inverse-transpose matrix assertions. No complementary convergence is assumed. -/
theorem dualBlockZero_rationalContinuation_of_iota (hrpos : 0 < r)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
      (unipotentHaar F.Carrier 0) μ)
    (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ) P)
    (f : (coefficientModel σ ℓ).toSubmodule) :
    ∃ Rd : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μ ν σ
          (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
          f (rankOneTrivialModelOne ψ)) Rd := by
  have hMd := (iotaMatrixAnalyticAssertions_firstDual_iff ψ σ ℓ
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier r) P).mp hIota
  obtain ⟨Rd, hRd⟩ := rationalContinuation_of_matrix F (ψ.scale (-1)) ν
    (inverseTransposePullback σ) (firstDualFunctional ψ σ ℓ) μ hrpos
    (isOfWhittakerType_firstDual ψ σ hσ) (firstDualFunctional_ne_zero ψ σ hℓ)
    hμ P hMd (r - 0 - 1) 0 (by omega)
    (translatedFirstDualModelEquiv ψ σ ℓ (blockWeylAt 0 r hrpos) f)
  have h1 : secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val =
      (rankOneTrivialModelOne (ψ.scale (-1))).val := by
    apply Subtype.ext
    funext g
    simp only [secondDualFunction_apply, rankOneTrivialModelOne_apply]
  refine ⟨Rd, ?_⟩
  unfold dualUnequalRankModelIntegralAt
  rw [h1]
  exact hRd

end RankOneBlockReduction

end Langlands.RankinSelberg
