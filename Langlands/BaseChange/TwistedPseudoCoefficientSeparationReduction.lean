import Langlands.BaseChange.TwistedPaleyWienerStatement
import Langlands.BaseChange.TwistedPseudoCoefficientSpectralConstruction
import Langlands.BaseChange.TwistedPseudoCoefficientSmallRank

/-! # Twisted pseudo-coefficients from spectral splitting and trace Paley–Wiener -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

/-- Trace realization and the twisted-character splitting imply the full existence statement. -/
def TwistedPseudoCoefficientSeparationReductionStatement.{u,v,z} : Prop :=
  TwistedTracePaleyWienerStatement.{u,v,z} →
  TwistedPseudoCoefficientSpectrumSplittingStatement.{u,v,z} →
  TwistedPseudoCoefficientExistenceStatement.{u,v,z}

/-- Apply trace Paley–Wiener to the constructed functional with the given Haar measure. -/
theorem twistedPseudoCoefficientExistence_of_spectrumSplitting.{u,v,z} :
    TwistedPseudoCoefficientSeparationReductionStatement.{u,v,z} := by
  intro hPW hsplit
  apply twistedPseudoCoefficientExistence_of_higherRanks.{u,v,z}
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  let : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro W _ _ τ hτ hdisc χ hχ A μ _
  obtain ⟨Φ, hc, hr, h1, h0⟩ := twistedPseudoCoefficientFunctionalExistence_of_spectrumSplitting
    hsplit F E σ l n hE hn W τ hτ hdisc χ hχ A μ
  obtain ⟨φ, hφ⟩ := hPW F E σ l n hE μ Φ hc hr
  refine ⟨φ, hχ, (hφ W τ hτ hdisc.2.1 A).trans h1, ?_⟩
  intro W' _ _ τ' hτ' hirr' htemp' hχ' hne A'
  exact (hφ W' τ' hτ' hirr' A').trans (h0 W' τ' hτ' hirr' htemp' hχ' hne A')

end Langlands.BaseChange
