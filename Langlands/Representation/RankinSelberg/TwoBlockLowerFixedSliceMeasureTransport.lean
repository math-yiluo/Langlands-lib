import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Group.GL.CountabilityProof

/-!
# Measures and slice transport for the Section 4.7 lower quotient

The lower measure is exactly the pushforward by the inverse block-rotation
homeomorphism. Compatibility and sigma-finiteness follow from the published
normalized standard quotient construction. Restriction commutes with this
pushforward, which transfers absolute integrability and both integrals.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFixedSlice

open MeasureTheory GeneralLinear QuotientIntegration TwoBlockLowerUnipotentQuotient

universe uF uE

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance measureTransportFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance measureTransportFieldValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance measureTransportLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance measureTransportFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance measureTransportFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance measureTransportGeneralLinearGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance measureTransportGeneralLinearLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance measureTransportGeneralLinearSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
variable [MeasurableSpace (LowerQuotient h F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)]

/-- The measure used on the lower quotient, with exactly the prescribed scale. -/
def lowerMeasure (νN : Measure (LeftUnipotentQuotient t F.Carrier)) :
    Measure (LowerQuotient h F.Carrier) :=
  Measure.map (lowerToStandard h F.Carrier).symm νN

/-- Restricting the transported measure to a determinant slice is the transport
of the standard measure restricted to the corresponding standard slice. -/
theorem lowerMeasure_restrict (νN : Measure (LeftUnipotentQuotient t F.Carrier)) (k : ℤ) :
    (lowerMeasure F h νN).restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k) =
      Measure.map (lowerToStandard h F.Carrier).symm
        (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t k)) := by
  let e := (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv
  have he := e.restrict_map νN (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)
  change (lowerMeasure F h νN).restrict _ =
    Measure.map (lowerToStandard h F.Carrier).symm
      (νN.restrict ((lowerToStandard h F.Carrier).symm ⁻¹'
        TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) at he
  rw [preimage_lowerToStandard_symm_determinantSlice] at he
  exact he

/-- Absolute integrability is preserved in both directions by the prescribed
restricted transport; no convergence assumption is hidden in an integral identity. -/
theorem integrable_lowerMeasure_iff
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (f : LowerQuotient h F.Carrier → E) (k : ℤ) :
    Integrable f ((lowerMeasure F h νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) ↔
      Integrable (fun q => f ((lowerToStandard h F.Carrier).symm q))
        (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t k)) := by
  rw [lowerMeasure_restrict]
  exact integrable_map_equiv
    (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv f

/-- Restricted complex and real integral transport, valid for every Banach-valued
function, including the actual integrand and its norm. -/
theorem integral_lowerMeasure
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (f : LowerQuotient h F.Carrier → E) (k : ℤ) :
    (∫ z, f z ∂(lowerMeasure F h νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) =
      ∫ q, f ((lowerToStandard h F.Carrier).symm q)
        ∂νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t k) := by
  rw [lowerMeasure_restrict]
  exact integral_map_equiv
    (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv f

/-- Sigma-finiteness of a standard quotient measure passes to its lower transport. -/
theorem sigmaFinite_lowerMeasure
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) [SigmaFinite νN] :
    SigmaFinite (lowerMeasure F h νN) :=
  (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.sigmaFinite_map

variable [MeasurableSpace (GeneralLinear (t + 1) F.Carrier)]
  [BorelSpace (GeneralLinear (t + 1) F.Carrier)]
variable [MeasurableSpace (upperUnipotent (t + 1) F.Carrier)]
  [BorelSpace (upperUnipotent (t + 1) F.Carrier)]

/-- The exact normalized standard quotient measure exists, and every compatible
measure and its prescribed lower transport are sigma-finite. -/
theorem compatible_measure_data :
    ∃ hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t),
      letI := hN
      (∃ νN : Measure (LeftUnipotentQuotient t F.Carrier),
        IsCompatible (upperUnipotent (t + 1) F.Carrier)
          (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN) ∧
      (∀ νN : Measure (LeftUnipotentQuotient t F.Carrier),
        IsCompatible (upperUnipotent (t + 1) F.Carrier)
          (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN →
        SigmaFinite νN ∧ SigmaFinite (lowerMeasure F h νN)) := by
  refine ⟨unipotentHaar_isMulRightInvariant F.Carrier t, ?_⟩
  refine ⟨unipotent_compatibleMeasureExists F.Carrier t, ?_⟩
  intro νN hνN
  let := hνN.regular
  let : T2Space (LeftUnipotentQuotient t F.Carrier) :=
    leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F.Carrier))
  let : LocallyCompactSpace (LeftUnipotentQuotient t F.Carrier) :=
    leftQuotient_locallyCompactSpace _
  let : SecondCountableTopology (LeftUnipotentQuotient t F.Carrier) :=
    ContinuousConstSMul.secondCountableTopology
  have hσ : SigmaFinite νN := inferInstance
  exact ⟨hσ, sigmaFinite_lowerMeasure F h νN⟩

end Langlands.RankinSelberg.TwoBlockLowerFixedSlice
