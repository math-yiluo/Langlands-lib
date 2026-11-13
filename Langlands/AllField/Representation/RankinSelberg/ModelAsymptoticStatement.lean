import Langlands.Representation.RankinSelberg.ModelAsymptoticStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
import Langlands.AllField.Representation.Whittaker.AsymptoticStatement
/-!
# Torus expansions in coefficient models

This is a conditional interface: the Whittaker-type torus expansion
`WhittakerTypeAsymptoticStatement` gives the expansion in the actual coefficient
models of JPSS integrals, for the topology of the same supplied data `T`. It does not assert the analytic expansion without its prerequisite.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding ModelAsymptoticTransferStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open scoped BigOperators

universe uF uV

/-- The Whittaker-type full-torus statement implies the expansion needed by JPSS
coefficient models, for every supplied `T : LocalFieldData F` and either character sign.
The implication retains the full Whittaker-type, possibly reducible scope. -/
def ModelAsymptoticTransferStatement : Prop :=
  WhittakerTypeAsymptoticStatement.{uF, uV} →
    ∀ (F : Type uF) [Field F]
      (T : LocalFieldData F),
      letI := T.topology
      ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
        (ψ : UnitaryAdditiveCharacter F)
        (θ : upperUnipotent (n + 1) F →* ℂˣ),
        (θ = standardCharacter ψ n ∨ θ = inverseStandardCharacter ψ n) →
        IsOfWhittakerType n θ π → CoefficientTorusExpansion θ π

end Langlands.AllField.RankinSelberg
