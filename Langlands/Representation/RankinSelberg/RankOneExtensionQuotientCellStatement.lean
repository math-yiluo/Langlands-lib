import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# The rank `t + 2` unipotent quotient in lower-block coordinates

Every compatible quotient measure on `N_(t+2) \ GL_(t+2)` is a positive finite
multiple of the pushforward of `|det m|⁻¹ dμbase(m) dx d^×a` along
`(N_(t+1) m, x, a) ↦ N_(t+2) [m, 0; x, a]`, for every compatible quotient
measure `μbase` on `N_(t+1) \ GL_(t+1)`. This module only defines the
proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear QuotientIntegration
open scoped ENNReal

universe uF

/-- Quotient-measure formula in lower-block coordinates. The representative
`Quotient.out q` is only used to write the map; the value
`N_(t+2) [m, 0; x, a]` and the density `|det m|⁻¹` do not depend on the
representative `m` of `q`. -/
def RankOneExtensionQuotientCellStatement : Prop :=
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
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (1 + t))],
    ∀ (μ : AdditiveHaarMeasure F.Carrier)
      (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (1 + t)) (unipotentHaar F.Carrier (1 + t)) μind →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        μind =
          c • Measure.map
            (fun q : LeftUnipotentQuotient t F.Carrier × (Fin (t + 1) → F.Carrier) ×
                F.Carrierˣ =>
              (Quotient.mk _ (rankOneExtensionLowerBlock t (Quotient.out q.1) q.2.1 q.2.2 :
                  Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) :
                LeftUnipotentQuotient (1 + t) F.Carrier))
            ((μbase.prod ((rowMeasure μ (t + 1)).prod
                (localMultiplicativeHaar F.Carrier))).withDensity
              (fun q => (F.canonicalTopologicalData.normalizedAbsHom
                (Quotient.out q.1).val.det : ℝ≥0∞)⁻¹))

end Langlands.RankinSelberg
