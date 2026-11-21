import Langlands.Global.AdelicLocalWavePacketStatement
import Langlands.Global.AdelicIwasawaCompatibleMeasureReduction
import Langlands.Global.AdelicIwasawaIntegrationProof
import Langlands.Global.AdelicParabolicModulusProof
import Langlands.GroupScheme.Rational.LeviRetraction

/-! # Geometric inputs for the bounded wave packet reduction -/

open CategoryTheory Langlands.GroupScheme

namespace Langlands.Global

/-- The Levi coordinate of the semidirect product gives a retraction onto `M`. -/
theorem leviProjectionExistence : LeviProjectionExistenceStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT _ _
  obtain ⟨U₀, r₀, hr₀, _⟩ := r.isCompatible.levi.exists_unipotentRadical
  exact ⟨leviRetraction l r₀ hr₀.1.isNormal, levi_comp_leviRetraction l r₀ hr₀.1.isNormal⟩

/-- The Iwasawa integration theorem and the modulus identification supply the compatible
Levi Haar measure, with the same normalizations as the wave packet statement. -/
theorem wavePacketIwasawaCompatibleMeasureExistence :
    WavePacketIwasawaCompatibleMeasureExistenceStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT hG hU K hK hKmax
  exact (iwasawaCompatibleMeasureIntegrationReduction
    AdelicGroupPoints.adelicIwasawaIntegration AdelicGroupPoints.adelicParabolicModulus)
    F G P M U A p iU l a r hG hU K hK hKmax

end Langlands.Global
