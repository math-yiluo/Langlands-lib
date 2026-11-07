import Langlands.Representation.RankinSelberg.LanglandsFactors

/-!
# Carrier-universe comparison for nongeneric pair epsilon factors

The classification-based constructor `langlandsPairEpsilonFactorOfClassification`
returns the epsilon certificate with saturated block universes
`IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW}`. Consumers such as
`LanglandsGammaFactor` use `IsLanglandsPairEpsilonFactor.{uF, uV, uW}` for the
same carriers. The statement below is the named comparison between the two:
the saturated certificate gives the certificate with block universes `uV` and
`uW`, with the same `e`. It is internal and has no literature source.
-/

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis PadicField.TopologicalData

universe uF uV uW

/-- For representations `π` of `GL_(r+1)(F)` on a carrier in `max uF uV` and
`σ` of `GL_(t+1)(F)` on a carrier in `max uF uW`, every `e = (c, m)` that is the
epsilon factor of `(π, σ)` with square-integrable data whose blocks lie in the
saturated universes `max uF uV` and `max uF uW` is also the epsilon factor of
`(π, σ)` with data whose blocks lie in `uV` and `uW`. The character, the
additive Haar measure and the ranks are arbitrary. -/
def LanglandsPairEpsilonUniverseComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (r t : ℕ)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))
    (e : ℂˣ × ℤ),
    IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e →
      IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e

/-- Given the comparison, existence of a saturated epsilon certificate for one
pair gives existence of the certificate with block universes `uV` and `uW`. -/
theorem exists_isLanglandsPairEpsilonFactor_of_universeComparison
    (hc : LanglandsPairEpsilonUniverseComparisonStatement.{uF, uV, uW})
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {r t : ℕ}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
    {σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}
    (h : ∃ e : ℂˣ × ℤ,
      IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e) :
    ∃ e : ℂˣ × ℤ, IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e :=
  h.imp fun e he => hc p F ψ ν r t π σ e he

end Langlands.RankinSelberg
