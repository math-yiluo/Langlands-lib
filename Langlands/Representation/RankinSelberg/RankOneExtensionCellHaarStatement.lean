import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData
import Langlands.Representation.RankinSelberg.Measures

/-!
# Haar measure of `GL_(t+2)` in upper-cell/lower-block coordinates

The published Haar measure on `GL_(t+2)` is a positive finite multiple of the
pushforward along `(y, m, x, a) ↦ u(y) * [m, 0; x, a]` of
`dy · |det m|⁻¹ dm · dx · d^×a`. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear
open scoped ENNReal

universe uF

/-- Haar measure on `GL_(t+2)` in upper-cell/lower-block coordinates, with an
existential positive finite constant and no normalization. -/
def RankOneExtensionCellHaarStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (t : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    ∀ μ : AdditiveHaarMeasure F.Carrier,
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        generalLinearHaar F.Carrier (1 + t) =
          c • Measure.map
            (fun q : (Fin (t + 1) → F.Carrier) × Langlands.GeneralLinear (t + 1) F.Carrier ×
                (Fin (t + 1) → F.Carrier) × F.Carrierˣ =>
              (rankOneExtensionUpperCell t q.1 *
                rankOneExtensionLowerBlock t q.2.1 q.2.2.1 q.2.2.2 :
                  Langlands.GeneralLinear ((1 + t) + 1) F.Carrier))
            (((rowMeasure μ (t + 1)).prod ((generalLinearHaar F.Carrier t).prod
                ((rowMeasure μ (t + 1)).prod (localMultiplicativeHaar F.Carrier)))).withDensity
              (fun q => (F.canonicalTopologicalData.normalizedAbsHom q.2.1.val.det : ℝ≥0∞)⁻¹))

end Langlands.RankinSelberg
