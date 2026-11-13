import Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportStatement
import Langlands.AllField.Group.GL.Padic
namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankIwasawaSupportStatement
open Langlands.AllField.RankinSelberg

universe uF

/-- Uniform compact rectangular support from bounded adjacent Iwasawa ratios. -/
def UnequalRankIwasawaSupportStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let r := n + (j + k + 1)
  ∀ R : ℝ, 0 < R →
    ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F), IsCompact C ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F)
        (x : Matrix (Fin j) (Fin (n + 1)) F)
        (u : Langlands.GeneralLinear (r + 1) F)
        (a : Fin (r + 1) → Fˣ)
        (κ : Langlands.GeneralLinear (r + 1) F),
        u ∈ GeneralLinear.upperUnipotent (r + 1) F →
        κ ∈ Conductor.integralSubgroup
          (ValuativeRel.valuation F).integer r →
        unequalRankMatrix j k g x =
          u * GeneralLinear.Iwasawa.diagonalUnits a * κ →
        (∀ i : Fin r,
          T.normalizedAbs ((a i.castSucc / a i.succ : Fˣ) :
            F) ≤ R) →
        x ∈ C

end Langlands.AllField.RankinSelberg
