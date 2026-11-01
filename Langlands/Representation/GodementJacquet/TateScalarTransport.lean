import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.Representation.Hecke.TestFunction
import Langlands.Representation.Smooth.SmallRealizationProof
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Exact multiplicative Haar transport from scalars to one-by-one matrices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF

section Coordinates

variable (K : Type uF) [Field K] [TopologicalSpace K] [IsTopologicalRing K]

/-- The scalar homomorphism and determinant are inverse in rank one. -/
def tateScalarEquiv : Kˣ ≃ₜ* Langlands.GeneralLinear 1 K where
  toFun := scalar
  invFun := determinant
  left_inv a := by
    apply Units.ext
    simp [determinant, scalar]
  right_inv := scalar_determinant_rankOne
  map_mul' := map_mul scalar
  continuous_toFun := (scalarContinuous (R := K) (n := 1)).continuous
  continuous_invFun := (determinantContinuous (R := K) (n := 1)).continuous

/-- Scalar coordinates on the full matrix space, including zero. -/
def tateMatrixScalarHomeomorph : Matrix (Fin 1) (Fin 1) K ≃ₜ K :=
  (Homeomorph.piUnique (fun _ : Fin 1 => Fin 1 → K)).trans
    (Homeomorph.piUnique (fun _ : Fin 1 => K))

omit [Field K] [IsTopologicalRing K] in
@[simp] theorem tateMatrixScalarHomeomorph_apply (A : Matrix (Fin 1) (Fin 1) K) :
    tateMatrixScalarHomeomorph K A = A 0 0 := rfl

/-- The matrix test viewed as a genuine scalar Schwartz--Bruhat function. -/
def tateScalarTest (Φ : MatrixTestFunction 0 K) : SchwartzBruhat K :=
  Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph K).symm Φ

omit [IsTopologicalRing K] in
@[simp] theorem tateScalarTest_scalar (Φ : MatrixTestFunction 0 K) (a : Kˣ) :
    tateScalarTest K Φ (a : K) = Φ (scalar a : Langlands.GeneralLinear 1 K).val := by
  change Φ (fun _ _ => (a : K)) = _
  apply congrArg Φ
  funext i j
  fin_cases i
  fin_cases j
  simp [scalar, Matrix.GeneralLinearGroup.coe_scalar]

theorem tateScalarEquiv_mem_integral (O : Subring K) (a : Kˣ) :
    tateScalarEquiv K a ∈ Conductor.integralSubgroup O 0 ↔ a ∈ integralUnits O := by
  rw [Conductor.mem_integralSubgroup, mem_integralUnits]
  change ((∀ i j : Fin 1, (scalar a : Langlands.GeneralLinear 1 K) i j ∈ O) ∧
    (∀ i j : Fin 1, (scalar a : Langlands.GeneralLinear 1 K)⁻¹ i j ∈ O)) ↔ _
  simp [← map_inv, scalar, Matrix.GeneralLinearGroup.coe_scalar]

end Coordinates

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance tateTransportTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance tateTransportValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance tateTransportLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance tateTransportT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance tateTransportSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance tateTransportMeasurable : MeasurableSpace F.Carrier := borel _
local instance tateTransportBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance tateTransportUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance tateTransportUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance tateTransportGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance tateTransportGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance tateTransportGLLocallyCompact (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance tateTransportGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

/-- Both multiplicative Haar measures give the integral units mass one, so
the scalar isomorphism preserves them without a normalization factor. -/
theorem tateScalarEquiv_measurePreserving :
    MeasurePreserving (tateScalarEquiv F.Carrier)
      (localMultiplicativeHaar F.Carrier) (generalLinearHaar F.Carrier 0) := by
  let e := tateScalarEquiv F.Carrier
  let μ := localMultiplicativeHaar F.Carrier
  let K := Conductor.levelOpenSubgroup F.Carrier 0 0
  have hpre : e ⁻¹' (K : Set (Langlands.GeneralLinear 1 F.Carrier)) =
      (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) := by
    ext a
    change e a ∈ Conductor.levelSubgroup F.Carrier 0 0 ↔ _
    rw [Conductor.levelSubgroup_zero]
    exact tateScalarEquiv_mem_integral F.Carrier _ a
  have hm : μ.map e (K : Set (Langlands.GeneralLinear 1 F.Carrier)) = 1 := by
    rw [Measure.map_apply (f := fun a => e a)
      e.continuous_toFun.measurable K.isOpen.measurableSet, hpre]
    exact localMultiplicativeHaar_integerUnits F.Carrier
  refine ⟨e.continuous.measurable, ?_⟩
  exact ((Measure.haarMeasure_eq_iff
    (compactOpenPositive K (Conductor.isCompact_levelOpenSubgroup F.Carrier 0 0))
    (μ.map e)).mpr hm).symm

/-- Integrability of every function transports with the canonical measures. -/
theorem integrable_tateScalarEquiv_iff (A : Langlands.GeneralLinear 1 F.Carrier → ℂ) :
    Integrable (fun a => A (tateScalarEquiv F.Carrier a))
      (localMultiplicativeHaar F.Carrier) ↔
    Integrable A (generalLinearHaar F.Carrier 0) :=
  (tateScalarEquiv_measurePreserving F).integrable_comp_emb
    (tateScalarEquiv F.Carrier).toHomeomorph.measurableEmbedding

/-- Actual integrals, including the totalized nonintegrable case, transport. -/
theorem integral_tateScalarEquiv (A : Langlands.GeneralLinear 1 F.Carrier → ℂ) :
    (∫ a, A (tateScalarEquiv F.Carrier a) ∂localMultiplicativeHaar F.Carrier) =
      ∫ g, A g ∂generalLinearHaar F.Carrier 0 :=
  (tateScalarEquiv_measurePreserving F).integral_comp
    (tateScalarEquiv F.Carrier).toHomeomorph.measurableEmbedding A

end Padic

end Langlands.GodementJacquet
