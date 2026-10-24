import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Whittaker.Iwasawa

/-! The spectral determinant weight in cumulative-product coordinates. -/

namespace Langlands.RankinSelberg

open scoped BigOperators

universe uF

/-- The actual integral subgroup has determinant norm one, and right
multiplication by any matrix with determinant norm one leaves the explicit
root-coordinate spectral product and its norm unchanged. -/
def RootSpectralWeightStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let A := Fin (n + 1) → F.Carrierˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  (∀ k : K, T.normalizedAbs (Matrix.det k.val.val) = 1) ∧
    ∀ (a : A) (k : Langlands.GeneralLinear (n + 1) F.Carrier),
      T.normalizedAbs (Matrix.det k.val) = 1 →
      ∀ s : ℂ,
        let g := GeneralLinear.Iwasawa.diagonalUnits (toDiagonal a) * k
        determinantWeight (normalizedAbsoluteValue T) g s =
          ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s) ∧
        ‖determinantWeight (normalizedAbsoluteValue T) g s‖ =
          ∏ i, T.normalizedAbs (a i : F.Carrier) ^ ((i.val + 1 : ℝ) * s.re)

end Langlands.RankinSelberg
