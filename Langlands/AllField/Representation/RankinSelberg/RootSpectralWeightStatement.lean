import Langlands.Representation.RankinSelberg.RootSpectralWeightStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-! The spectral determinant weight in cumulative-product coordinates. -/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding RootSpectralWeightStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open scoped BigOperators

universe uF

/-- The actual integral subgroup has determinant norm one, and right
multiplication by any matrix with determinant norm one leaves the explicit
root-coordinate spectral product and its norm unchanged. -/
def RootSpectralWeightStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let A := Fin (n + 1) → Fˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  (∀ k : K, T.normalizedAbs (Matrix.det k.val.val) = 1) ∧
    ∀ (a : A) (k : Langlands.GeneralLinear (n + 1) F),
      T.normalizedAbs (Matrix.det k.val) = 1 →
      ∀ s : ℂ,
        let g := GeneralLinear.Iwasawa.diagonalUnits (toDiagonal a) * k
        determinantWeight (normalizedAbsoluteValue T) g s =
          ∏ i, (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s) ∧
        ‖determinantWeight (normalizedAbsoluteValue T) g s‖ =
          ∏ i, T.normalizedAbs (a i : F) ^ ((i.val + 1 : ℝ) * s.re)

end Langlands.AllField.RankinSelberg
