import Langlands.Global.AdelicEisensteinAmbientShiftProof
import Langlands.Global.AdelicRelativeWavePacketCompression
import Langlands.Global.AdelicStandardWavePacketTransport
import Langlands.Global.AdelicWavePacketRationalInvariance

/-! # Completeness on the relative quotient from full-quotient completeness -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

/-- Completeness of the full packets and rapid decay imply completeness of the standard
relative packets on the canonical quotient. -/
def RelativeWavePacketCompletenessFromFullStatement : Prop :=
  WavePacketCompletenessStatement → WavePacketRapidDecayStatement →
    RelativeWavePacketCompletenessStatement

/-- The full completeness proposition implies the version for a prescribed standard family
because the same full packet functions occur for that family. -/
theorem standardWavePacketCompleteness_of_full (hFull : WavePacketCompletenessStatement) :
    StandardWavePacketCompletenessStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P₀ _ p₀ hp₀ hmin hK₀ f hf hOrth
  apply hFull F G hG K rho hsmooth hcalc hKmax hrho ⟨P₀, inferInstance, p₀, hp₀, hmin, hK₀⟩ f hf
  intro P M U A _ _ _ _ p hp iU l hUp a r _ _ _ hA hT hU hK n e k v c E D hv hc hD hE hreg
  let Θ (g : AdelicGroupPoints F G) :=
    ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)
  have hΘ : IsWavePacket F G K rho hsmooth hcalc Θ :=
    ⟨P, M, U, A, inferInstance, inferInstance, inferInstance, inferInstance, p, hp, iU, l, hUp,
      a, r, inferInstance, inferInstance, inferInstance, hA, hT, hU, hK, n, e, k, v, c, E, D,
      hv, hc, hD, hE, hreg, rfl⟩
  obtain ⟨P', M', U', A', _, _, _, _, p', _, iU', l', a', r', _, _, _, hA', hT', hle, hU', hK', hΘ'⟩ :=
    standardWavePacketTransport F G P₀ hG p₀ hmin K rho hsmooth hcalc Θ hΘ
  exact hOrth P' M' U' A' p' iU' l' a' r' hA' hT' hle hU' hK' Θ hΘ'

/-- Full completeness and rapid decay yield relative completeness, with decay used at exponent
zero to supply square integrability. -/
theorem relativeWavePacketCompleteness_of_full : RelativeWavePacketCompletenessFromFullStatement := by
  intro hFull hDecay
  have hRegular : EisensteinRegularParameterStatement.{0} := by
    intro F _ G P M A _ p l a r _ _ _ hA hT hG R
    let : Smooth G.X.hom := hG.smooth
    exact r.regularParameter_nonempty hA hT R
  exact relativeWavePacketCompleteness_of_standard (standardWavePacketCompleteness_of_full hFull)
    hDecay (eisensteinContinuationAmbientShift_of_regularParameter hRegular)

end Langlands.Global
