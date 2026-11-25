import Langlands.TraceFormula.ExtendTwistedGeometricMeasures
import Langlands.TraceFormula.SingleOrbitSimpleTrace

/-! # Recovering a local orbital identity from two isolated trace identities -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Langlands.BaseChange
open scoped ENNReal

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H] [MeasurableSpace H]

/-- An isolated trace identity for a calibration pair determines the ratio
of the two fixed geometric weights. A second trace identity with the same
comparison constant then gives equality of the local orbital values. -/
def CalibratedTraceExtractionStatement : Prop :=
  ∀ [IsTopologicalGroup G] [BorelSpace G] [IsTopologicalGroup H] [BorelSpace H]
    (R : Subgroup G) (S : Subgroup H) (θG : G →* G) (θH : H →* H)
    (r : G) (s : H) (μG : Measure G) (μH : Measure H)
    (dG : TwistedGeometricMeasures R θG r μG) (dH : TwistedGeometricMeasures S θH s μH)
    (f : Bool → G → ℂ) (φ : Bool → H → ℂ)
    (ordinaryTrace twistedTrace ordinaryLocal twistedLocal : Bool → ℂ)
    (ordinaryExterior twistedExterior c : ℂ),
    ordinaryExterior ≠ 0 → c ≠ 0 →
    ordinaryLocal false ≠ 0 → twistedLocal false = ordinaryLocal false →
    (∀ j, dG.orbitalValue (f j) = ordinaryLocal j * ordinaryExterior) →
    (∀ j, dH.orbitalValue (φ j) = twistedLocal j * twistedExterior) →
    (dG.orbitalValue (f false) ≠ 0 → dG.rational Set.univ ≠ ⊤) →
    (∀ j, ordinaryTrace j = dG.term (f j)) →
    (∀ j, twistedTrace j = dH.term (φ j)) →
    (∀ j, twistedTrace j = c * ordinaryTrace j) →
    twistedLocal true = ordinaryLocal true

theorem calibratedTraceExtraction :
    CalibratedTraceExtractionStatement (G := G) (H := H) := by
  intro _ _ _ _ R S θG θH r s μG μH dG dH f φ ordinaryTrace twistedTrace ordinaryLocal twistedLocal
    ordinaryExterior twistedExterior c hExterior hc hloc hcal hFactorG hFactorH hFinite hG hH hCompare
  let a := ((dG.rational Set.univ).toReal : ℂ) * ordinaryExterior
  let b := ((dH.rational Set.univ).toReal : ℂ) * twistedExterior
  have ha : a ≠ 0 :=
    mul_ne_zero (dG.covolume_ne_zero (hFinite (hFactorG false ▸ mul_ne_zero hloc hExterior)))
      hExterior
  have htermG (j : Bool) : ordinaryTrace j = a * ordinaryLocal j := by
    rw [hG]
    change ((dG.rational Set.univ).toReal : ℂ) * dG.orbitalValue (f j) = _
    rw [hFactorG]
    dsimp [a]
    ac_rfl
  have htermH (j : Bool) : twistedTrace j = b * twistedLocal j := by
    rw [hH]
    change ((dH.rational Set.univ).toReal : ℂ) * dH.orbitalValue (φ j) = _
    rw [hFactorH]
    dsimp [b]
    ac_rfl
  have hweight (j : Bool) : b * twistedLocal j = (c * a) * ordinaryLocal j := by
    rw [← htermH, hCompare, htermG, mul_assoc c a]
  have hb : b = c * a :=
    mul_right_cancel₀ hloc (by simpa only [hcal] using hweight false)
  exact mul_left_cancel₀ (mul_ne_zero hc ha) (by simpa only [hb] using hweight true)

end Langlands.TraceFormula
