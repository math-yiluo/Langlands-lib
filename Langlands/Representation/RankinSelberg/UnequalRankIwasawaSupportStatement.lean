import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.LocalField.Normalization.Definitions

namespace Langlands.RankinSelberg

universe uF

/-- Uniform compact rectangular support from bounded adjacent Iwasawa ratios. -/
def UnequalRankIwasawaSupportStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let r := n + (j + k + 1)
  ∀ R : ℝ, 0 < R →
    ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier), IsCompact C ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
        (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
        (u : Langlands.GeneralLinear (r + 1) F.Carrier)
        (a : Fin (r + 1) → F.Carrierˣ)
        (κ : Langlands.GeneralLinear (r + 1) F.Carrier),
        u ∈ GeneralLinear.upperUnipotent (r + 1) F.Carrier →
        κ ∈ Conductor.integralSubgroup
          (ValuativeRel.valuation F.Carrier).integer r →
        unequalRankMatrix j k g x =
          u * GeneralLinear.Iwasawa.diagonalUnits a * κ →
        (∀ i : Fin r,
          T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) :
            F.Carrier) ≤ R) →
        x ∈ C

end Langlands.RankinSelberg
