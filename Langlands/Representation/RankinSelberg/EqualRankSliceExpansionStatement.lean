import Langlands.Representation.RankinSelberg.DeterminantSlices

/-!
# Conditional equal-rank determinant-series expansion

JPSS (1983), Section 4.2, (4.2.2), printed page 407: at any supplied
convergent parameter, the actual equal-rank integral is the absolutely
summable unordered sum of its determinant-slice coefficients with weight
`(q^(-s))^m`. All coefficients at zero are integrable on their slices.
This module states the conditional partition argument; it does not prove it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.HarmonicAnalysis
open MeasureTheory

universe uF

/-- Conditional partition content of JPSS (4.2.2), for any measure on the
Borel structure of the actual quotient: global convergence at `s` gives
slice integrability at zero, absolute summability of the weighted scalar
coefficients, and their `HasSum` to the actual integral at `s`. -/
def EqualRankSliceExpansionStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ),
    EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s →
      SliceIntegrable T μ
        (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0) ∧
      Summable (fun m : ℤ =>
        ‖equalRankSliceCoefficient T μ ψ W W' Φ m *
          spectralPoint T.residueCardinality s ^ m‖) ∧
      HasSum (fun m : ℤ =>
        equalRankSliceCoefficient T μ ψ W W' Φ m *
          spectralPoint T.residueCardinality s ^ m)
        (equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ s)

end Langlands.RankinSelberg
