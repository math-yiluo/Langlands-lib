import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport
import Langlands.Representation.RankinSelberg.DualModels

/-! Raw original and inverse-transpose bounds from matrix data on the actual model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear Topology Conductor GodementJacquet HarmonicAnalysis Whittaker
open scoped ENNReal NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelDataTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance modelDataValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance modelDataLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance modelDataT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance modelDataSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance modelDataMeasurable : MeasurableSpace F.Carrier := borel _
local instance modelDataBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance modelDataGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance modelDataGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance modelDataGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance modelDataGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData


local instance modelDataUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance modelDataUnitsLocallyCompact : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace
local instance modelDataUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance modelDataUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩


variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ n σ)
  (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)

/-- Genuine raw matrix convergence for this actual coefficient-model vector,
with a possibly test-dependent unshifted half-plane. -/
def RawModelMatrixConvergence : Prop :=
  ∀ Φ : MatrixTestFunction n F.Carrier, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
    GodementJacquet.Padic.MatrixConverges F Φ s (glModelFunction ψ n σ ℓ w)

/-- The corresponding genuine raw inverse-transpose matrix bound. -/
def RawModelIotaMatrixConvergence : Prop :=
  ∀ Φ : MatrixTestFunction n F.Carrier, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
    GodementJacquet.Padic.MatrixConverges F Φ s (coefficientIota (glModelFunction ψ n σ ℓ w))

/-- Evaluation on the actual image realizes its original model function
as an actual coefficient, with no equivalence from the original carrier. -/
theorem coefficientModelEvaluation_coefficient :
    (fun g => (coefficientModelEvaluation σ ℓ).val
      (glModelRepresentation ψ n σ ℓ g w)) = glModelFunction ψ n σ ℓ w := by
  funext g
  change w.val.val (1 * g) = w.val.val g
  rw [one_mul]

/-- Matrix bounds on the actual model representation give raw convergence
of the original function represented by each of its vectors. -/
theorem rawModelMatrixConvergence_of_modelMatrix (hσ : IsSmooth σ)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ n σ ℓ).toSubmodule) (glModelRepresentation ψ n σ ℓ)) :
    RawModelMatrixConvergence F ψ σ ℓ w := by
  intro Φ
  obtain ⟨b, hb⟩ := @whittakerCoefficient_matrixConvergesOnRight_of_matrix
    p _ F n (glCoefficientModel ψ n σ ℓ).toSubmodule inferInstance inferInstance ψ
    (glModelRepresentation ψ n σ ℓ) (glModel_isSmooth ψ n σ hσ ℓ)
    (coefficientModelEvaluation σ ℓ) w hMatrix Φ
  refine ⟨b, fun s hs => ?_⟩
  refine (hb s hs).congr (g := matrixIntegrand abv Φ s (glModelFunction ψ n σ ℓ w))
    (Filter.Eventually.of_forall fun g => ?_)
  unfold matrixIntegrand
  have he := congrFun (coefficientModelEvaluation_coefficient F ψ σ ℓ w) g
  exact congrArg (fun z : ℂ => Φ g.val * z * determinantWeight abv g s) he

/-- Raw inverse-transpose convergence for a coefficient of an abstract
smooth representation, before specializing to a coefficient-model carrier. -/
theorem whittakerCoefficientIota_matrixConvergesOnRight_of_iota
    (hσ : IsSmooth σ) (v : V)
    (hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F σ)
    (Φ : MatrixTestFunction n F.Carrier) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → GodementJacquet.Padic.MatrixConverges F Φ s
      (coefficientIota (fun g => ℓ.val (σ g v))) := by
  have hM := matrixConvergesOnRight_inverseTransposePullback F σ hIota
  obtain ⟨b, hb⟩ := whittakerCoefficient_matrixConvergesOnRight_of_matrix F (ψ.scale (-1))
    (inverseTransposePullback σ) (inverseTransposePullback_isSmooth σ hσ)
    (firstDualFunctional ψ σ ℓ) v hM (matrixWeylTranslate n Φ)
  refine ⟨b, fun s hs => ?_⟩
  apply (GodementJacquet.Padic.matrixConverges_weylTranslate_dualFunction_iff F Φ s _).mp
  refine (hb s hs).congr
    (g := matrixIntegrand abv (matrixWeylTranslate n Φ) s
      (dualFunction n (fun g => ℓ.val (σ g v))))
    (Filter.Eventually.of_forall fun g => ?_)
  exact congrArg (fun z : ℂ => (matrixWeylTranslate n Φ) g.val * z *
    determinantWeight abv g s) (congrFun (dualFunction_coefficient ψ σ ℓ v) g).symm

/-- Transformed matrix bounds on the actual model give raw convergence of
its original inverse-transpose function for every full-matrix test. -/
theorem rawModelIotaMatrixConvergence_of_modelIota (hσ : IsSmooth σ)
    (hIota : GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ n σ ℓ).toSubmodule) (glModelRepresentation ψ n σ ℓ)) :
    RawModelIotaMatrixConvergence F ψ σ ℓ w := by
  intro Φ
  obtain ⟨b, hb⟩ := @whittakerCoefficientIota_matrixConvergesOnRight_of_iota
    p _ F n (glCoefficientModel ψ n σ ℓ).toSubmodule inferInstance inferInstance ψ
    (glModelRepresentation ψ n σ ℓ) (coefficientModelEvaluation σ ℓ)
    (glModel_isSmooth ψ n σ hσ ℓ) w hIota Φ
  refine ⟨b, fun s hs => ?_⟩
  refine (hb s hs).congr
    (g := matrixIntegrand abv Φ s (coefficientIota (glModelFunction ψ n σ ℓ w)))
    (Filter.Eventually.of_forall fun g => ?_)
  exact congrArg (fun z : ℂ => Φ g.val * z * determinantWeight abv g s)
    (congrFun (coefficientModelEvaluation_coefficient F ψ σ ℓ w)
      (inverseTranspose (n + 1) F.Carrier g))

/-- Both actual raw bounds follow from the matrix functional-equation data
on exactly the model representation occurring in the target statement. -/
theorem rawModel_pair_convergence_of_data
    (hσ : IsSmooth σ) (ν : AdditiveHaarMeasure F.Carrier)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hData : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
      (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) P PDual c a) :
    RawModelMatrixConvergence F ψ σ ℓ w ∧ RawModelIotaMatrixConvergence F ψ σ ℓ w :=
  ⟨rawModelMatrixConvergence_of_modelMatrix F ψ σ ℓ w hσ hData.1.1,
    rawModelIotaMatrixConvergence_of_modelIota F ψ σ ℓ w hσ hData.2.1.1⟩

end Langlands.RankinSelberg
