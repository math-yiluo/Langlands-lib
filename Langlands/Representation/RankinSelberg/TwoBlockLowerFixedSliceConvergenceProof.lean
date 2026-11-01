import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceConvergenceStatement
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant
import Langlands.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity
import Langlands.Representation.RankinSelberg.QuotientTorusEnvelope

/-! # Absolute convergence on each Section 4.7 lower determinant slice -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockJacquet TwoBlockDeformation TwoBlockConvergence TwoBlockLowerUnipotentQuotient
  TwoBlockLowerUnfolding TwoBlockLowerFixedSlice

universe uF uV uW

/-- Fixed-slice absolute convergence of the actual lower integrand, with the
prescribed compatible quotient measures and supplied opposite-twist data. -/
theorem twoBlockLowerFixedSliceConvergence :
    TwoBlockLowerFixedSliceConvergenceStatement.{uF, uV, uW} := by
  intro p _ F
  dsimp only
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  let := F.canonicalTopologicalData.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν t m h
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  let : MeasurableSpace (GeneralLinear (t + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (t + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient t F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LowerQuotient h F.Carrier) := borel _
  let : BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
  obtain ⟨hN, hmeasure⟩ := compatible_measure_data F h
  refine ⟨hN, ?_⟩
  let := hN
  refine ⟨hmeasure.1, hmeasure.2, ?_⟩
  intro V _ _ π hπ lambda W _ _ τ hτ ell
  have hjlt : m 1 < t := by
    have hh : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    omega
  let j : Fin t := ⟨m 1, hjlt⟩
  obtain ⟨C, hC⟩ :=
    exists_summable_integrand_majorant F h ψ ν π hπ lambda τ hτ ell j rfl
  refine ⟨C, fun u hu νN hνN f Wtest Φ k => ?_⟩
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let E : LowerQuotient h F.Carrier → ℂ := integrand ellu f Wtest.val Φ ν.val
  have hE : Measurable E :=
    integrand_measurable ellu f π hπ.1.1 lambda Wtest Φ ν.val
  have hEs : Measurable (fun q => E ((lowerToStandard h F.Carrier).symm q)) :=
    hE.comp (canonicalLowerToStandardHomeomorph F h).symm.continuous.measurable
  obtain ⟨A, _, hsum, hbound⟩ := hC u hu f Wtest Φ
  have hEst : Integrable (fun q => E ((lowerToStandard h F.Carrier).symm q)) νN := by
    apply QuotientTorusEnvelope.integrable_of_summable_torus_bound
      F F.canonicalTopologicalData t νN hνN
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      (uniformizerUnit_isUniformizingElement F) _ hEs A _ hsum
    intro lam k hk
    exact hbound lam k ((mem_integralOpen F k).mpr
      ((Conductor.mem_integralSubgroup _ t k).mp hk))
  have hslice := hEst.restrict
    (s := RankinSelberg.determinantSlice F.canonicalTopologicalData t k)
  exact ⟨hE, (integrable_lowerMeasure_iff F h νN E k).mpr hslice, hslice,
    integral_lowerMeasure F h νN E k,
    integral_lowerMeasure F h νN (fun z => ‖E z‖) k⟩

end Langlands.RankinSelberg
