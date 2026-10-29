import Langlands.Representation.Whittaker.BruhatFiberAverage
import Langlands.Representation.Whittaker.Distribution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Haar measure prerequisites for the Shalika argument -/

namespace Langlands.Whittaker

open Langlands.GeneralLinear MeasureTheory

universe uF

/-- Actual p-adic unipotent and Bruhat fiber Haar measures have the invariances
needed for orbital integration and the exchange of the two unipotent factors. -/
def BruhatHaarMeasureStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ n : ℕ,
      let U := upperUnipotent (n + 1) F.Carrier
      letI := borel U
      (∃ μ : Measure U, μ.IsHaarMeasure) ∧
      (∀ (μ : Measure U) [μ.IsHaarMeasure],
        SigmaFinite μ ∧ μ.IsMulRightInvariant ∧
          Measure.map (weylTransposeUnipotent n F.Carrier) μ = μ) ∧
      ∀ w : Equiv.Perm (Fin (n + 1)),
        let P := permutationUnipotentPlus (n + 1) F.Carrier w
        letI := borel P
        (∃ ν : Measure P, ν.IsHaarMeasure) ∧
        (∀ (ν : Measure P) [ν.IsHaarMeasure],
          SigmaFinite ν ∧ ν.IsMulRightInvariant)

end Langlands.Whittaker
