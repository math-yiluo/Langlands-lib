import Langlands.Representation.RankinSelberg.LanglandsFactorDescent

/-!
# Existence of epsilon factors of arbitrary irreducible pairs

Henniart 2002, Section 2.8, printed page 596, identifies an irreducible
representation `π` with a nonzero finite sum `∑ π_i` of essentially
square-integrable classes: `π` is the unique irreducible quotient of
`i(π_1, …, π_r)` for nonincreasing exponents. For `π = ∑ π_i` and
`π' = ∑ π'_j` it gives `ε(s, π × π') = ∏_(i,j) ε(s, π_i × π'_j, ψ)`. The
statement below asserts that this factor exists, as an actual
`IsLanglandsPairEpsilonFactor` certificate, for every irreducible admissible
pair of positive ranks. JPSS 1983, (9.4), defines only the L-factor of such
pairs.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis PadicField.TopologicalData

universe uF uV uW

/-- Henniart 2002, 2.8, printed page 596: for a nontrivial additive character
`ψ`, a Haar measure `ν` self-dual for `ψ`, and irreducible admissible
representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)` of either rank
order, some `e = (c, m)`, representing `c q^(-ms)`, is the epsilon factor of the
pair: both representations are Langlands quotients of square-integrable data
in their carrier universes, and for every such pair of data `e` is the product
of the JPSS epsilon factors of all pairs of blocks. -/
def LanglandsPairEpsilonFactorExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)),
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible π.representation) →
    (letI := F.canonicalTopologicalData.topology; π.IsAdmissible) →
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible σ.representation) →
    (letI := F.canonicalTopologicalData.topology; σ.IsAdmissible) →
    ∃ e : ℂˣ × ℤ,
      IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν.val π σ e

/-- The statement follows from square-integrable exhaustion and classification
at both carrier universes and existence of the epsilon factors of all pairs of
square-integrable blocks, through `langlandsPairEpsilonFactorOfClassification`.
None of these inputs is proved here. -/
theorem langlandsPairEpsilonFactorExistence_of_classification
    (hex : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      Classification.SquareIntegrableLanglandsExhaustion.{uF, uV}
          F F.canonicalTopologicalData ∧
        Classification.SquareIntegrableLanglandsExhaustion.{uF, uW}
          F F.canonicalTopologicalData)
    (hcl : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      Classification.SquareIntegrableLanglandsClassification.{uF, uV}
          F F.canonicalTopologicalData ∧
        Classification.SquareIntegrableLanglandsClassification.{uF, uW}
          F F.canonicalTopologicalData)
    (hb : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
      (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
      (r t : ℕ)
      (d : SquareIntegrableLanglandsDatum.{max uF uV, uF} F.canonicalTopologicalData (r + 1))
      (d' : SquareIntegrableLanglandsDatum.{max uF uW, uF} F.canonicalTopologicalData (t + 1)),
      SquareIntegrableDataEpsilonExistence F ψ ν.val d d') :
    LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t π σ hπ _ hσ _
  exact ⟨_, (langlandsPairEpsilonFactorOfClassification F ψ ν.val π σ hπ hσ
    (hex p F).1 (hex p F).2 (hcl p F).1 (hcl p F).2
    fun d d' _ _ => hb p F ψ ν r t d d').property⟩

end Langlands.RankinSelberg
