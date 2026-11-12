import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # A single integral cuspidal line for a supplied Speh representation -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every supplied Speh representation has an actual supercuspidal support
contained in the integral real-twist line of one cuspidal datum. The base
datum absorbs the centered half-integral shift of the Speh induction. -/
def SpehIntegralLineSupport : Prop :=
  letI := T.topology
  ∀ (d : SpehDatum.{uF, uV} F T)
    (S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier)),
    d.IsSpeh S →
      ∃ (ρ : T.CuspidalDatum.{max uF uV, uF})
        (s : Multiset (T.CuspidalDatum.{max uF uV, uF})),
        T.IsSupercuspidalSupport S s ∧
          ∀ τ ∈ s, ∃ m : ℤ, τ = ρ.twist (m : ℝ)

end Langlands.Classification
