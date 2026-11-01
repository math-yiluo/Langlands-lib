import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalCompactDual
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelApproximation

/-! Extension of compact signed dual extraction to actual coefficient-model vectors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Induction Topology
open RankOneIwasawa RankOneBox CompactWhittakerSynthesis CompactWhittakerApproximation
open scoped NNReal ENNReal

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalModelDualTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalModelDualValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalModelDualLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalModelDualT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance principalModelDualSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance principalModelDualMeasurable : MeasurableSpace F.Carrier := borel _
local instance principalModelDualBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance principalModelDualNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance principalModelDualNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalModelDualNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance principalModelDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalModelDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalModelDualGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance principalModelDualGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance principalModelDualNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance principalModelDualTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance principalModelDualUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance principalModelDualUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance principalModelDualUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The literal weighted signed-Weyl Fourier restriction of a group function. -/
def principalModelFourierIntegrand
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (h : Langlands.GeneralLinear (m + 2) F.Carrier) : ℂ :=
  let q := F.canonicalTopologicalData.additiveConductor ψ
  let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
  (determinantWeight abv h s * W h) *
    rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val

/-- The true weighted block restriction, retaining the principal parameter. -/
def principalModelBlockIntegrand (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      (Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)) : ℂ :=
  determinantWeight abv z.2.1 s * W (principalSignedBlockPoint F m z.1 z.2)

private theorem continuous_principalModel_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F.Carrier) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (rankInclusionContinuous 1).continuous.comp ih

/-- Continuity of the literal block evaluation map gives its required
measurability without any quotient or orbit identification. -/
theorem continuous_principalSignedBlockPoint (m : ℕ) :
    Continuous (fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      (Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) =>
      principalSignedBlockPoint F m z.1 z.2) := by
  have hgen (n r j k : ℕ) (hr : r = n + (j + k + 1)) :
      Continuous (fun z : Langlands.GeneralLinear (n + 1) F.Carrier ×
        Matrix (Fin j) (Fin (n + 1)) F.Carrier =>
        AdjacentBlockReduction.blockMatrixAt j k hr z.1 z.2) := by
    subst r
    change Continuous (fun z : Langlands.GeneralLinear (n + 1) F.Carrier ×
      Matrix (Fin j) (Fin (n + 1)) F.Carrier => unequalRankMatrix j k z.1 z.2)
    exact ((continuous_principalModel_appendIdentity F n (j + k + 1)).comp continuous_fst).mul
      ((continuous_rectangularUnipotent j k).comp continuous_snd)
  have hb := hgen 0 (m + 1) m 0 (by omega)
  exact ((hb.comp continuous_snd).mul_const _).mul
    ((continuous_inverseTranspose _ _).comp continuous_fst)

/-- The compact distribution identity extends to every actual smooth
coefficient-model vector when its two genuine weighted restrictions converge.
No gamma equation or original irreducibility is used. -/
theorem principalModelDual_pairing
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (f : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) (s : ℂ)
    (hi : Integrable (principalModelFourierIntegrand F ψ ν m a s
        (glModelFunction ψ (m + 1) σ ℓ f)) (generalLinearHaar F.Carrier (m + 1)))
    (hj : Integrable (principalModelBlockIntegrand F m s
        (glModelFunction ψ (m + 1) σ ℓ f))
      ((principalAveragingMeasure F (n := m + 1) a
        (boxExtractionConstant F (n := m + 1)
          (F.canonicalTopologicalData.additiveConductor ψ + a)
          (F.canonicalTopologicalData.additiveConductor ψ) a)).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)))) :
    (∫ h, principalModelFourierIntegrand F ψ ν m a s
      (glModelFunction ψ (m + 1) σ ℓ f) h ∂generalLinearHaar F.Carrier (m + 1)) =
    ∫ z, principalModelBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ f) z
      ∂(principalAveragingMeasure F (n := m + 1) a
        (boxExtractionConstant F (n := m + 1)
          (F.canonicalTopologicalData.additiveConductor ψ + a)
          (F.canonicalTopologicalData.additiveConductor ψ) a)).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  let q := F.canonicalTopologicalData.additiveConductor ψ
  let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
  let C := boxExtractionConstant F (n := m + 1) (q + a) q a
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let L := fun h : Langlands.GeneralLinear (m + 2) F.Carrier =>
    determinantWeight abv h s * rectangularFourierIntegral ψ ν Ψ
      (rankOneSignedWeyl (m + 1) * h).val
  let R := fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      (Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) =>
    determinantWeight abv z.2.1 s
  have hc (g : CompactFunctions (upperUnipotent (m + 2) F.Carrier)
      (characterRepresentation (standardCharacter ψ (m + 1)))) :
      (∫ h : Langlands.GeneralLinear (m + 2) F.Carrier,
        L h * eval _ _ g.val h ∂generalLinearHaar F.Carrier (m + 1)) =
      ∫ z, R z * eval _ _ g.val (principalSignedBlockPoint F m z.1 z.2)
        ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
    have h := (principalCompactDual_pairing_weighted F ψ ν hsd ha hA g s).2.2
    simpa only [L, R, principalCompactDualIntegrand, mul_right_comm] using h
  have hpoint (h : Langlands.GeneralLinear (m + 2) F.Carrier) :
      L h * glModelFunction ψ (m + 1) σ ℓ f h =
        principalModelFourierIntegrand F ψ ν m a s (glModelFunction ψ (m + 1) σ ℓ f) h := by
    simp only [L, principalModelFourierIntegrand, Ψ, q, mul_right_comm]
  have hi' : Integrable (fun h : Langlands.GeneralLinear (m + 2) F.Carrier =>
      L h * glModelFunction ψ (m + 1) σ ℓ f h)
      (generalLinearHaar F.Carrier (m + 1)) :=
    hi.congr (g := fun h => L h * glModelFunction ψ (m + 1) σ ℓ f h)
      (Filter.Eventually.of_forall fun h => (hpoint h).symm)
  have hj' : Integrable (fun z => R z * glModelFunction ψ (m + 1) σ ℓ f
      (principalSignedBlockPoint F m z.1 z.2))
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) := hj
  have he := weighted_glModel_integral_eq_of_compact F ψ (m + 1) σ hσ ℓ
    (generalLinearHaar F.Carrier (m + 1))
    (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)))
    id (fun z => principalSignedBlockPoint F m z.1 z.2) L R measurable_id
    (continuous_principalSignedBlockPoint F m).measurable hc f hi' hj'
  exact (integral_congr_ae (Filter.Eventually.of_forall fun h => (hpoint h).symm)).trans he

end Langlands.RankinSelberg
