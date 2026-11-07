import Langlands.Representation.RankinSelberg.LanglandsFactors
import Langlands.Representation.RankinSelberg.LanglandsPairEpsilonFactorExistenceStatement
import Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor

/-!
# Classification and integral epsilon factors of generic pairs

`IsLanglandsPairEpsilonFactor` defines the epsilon factor of an irreducible pair
through square-integrable Langlands data, as the product of the JPSS epsilon
factors of all pairs of blocks (Henniart 2002, Section 2.8, printed page 596).
`IsPadicSymmetricEpsilonFactor` is the JPSS epsilon factor of the pair itself,
read from the local functional equation of its Whittaker models. The statement
below asserts that for a generic pair every value certified by the first
relation satisfies the second. The three corollaries record what a proof of the
statement supplies to consumers; the statement itself is not proved.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker PadicField.TopologicalData

universe uF uV uW

/-- For a nontrivial additive character `ψ`, a Haar measure `ν` self-dual for
`ψ`, and irreducible admissible representations `π` of `GL_(r+1)(F)` and `σ` of
`GL_(t+1)(F)` of either rank order, both generic with respect to `ψ`: every
`e = (c, m)`, representing `c q^(-ms)`, that is the epsilon factor of the pair
through square-integrable Langlands data (the product of the JPSS epsilon
factors of all block pairs, Henniart 2002, 2.8) is also the JPSS epsilon factor
of the pair `(π, σ)` itself. -/
def GenericLanglandsPairEpsilonFactorComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
    (σ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)),
    (letI := F.canonicalTopologicalData.topology; IsGeneric ψ r π.representation) →
    (letI := F.canonicalTopologicalData.topology; IsGeneric ψ t σ.representation) →
    ∀ e : ℂˣ × ℤ, IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e →
      letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricEpsilonFactor F ψ ν.val π.representation σ.representation e

namespace GenericLanglandsPairEpsilonFactorComparisonStatement

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
  {r t : ℕ}
  {π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)}
  {σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier)}

/-- Under the comparison, a classification epsilon factor of a generic pair is
the published constructed integral epsilon data of the pair. -/
theorem eq_genericSymmetricEpsilonData
    (h : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uV, uW})
    (hπ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ r π.representation)
    (hσ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ t σ.representation)
    {e : ℂˣ × ℤ} (he : IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e) :
    letI := F.canonicalTopologicalData.topology
    e = genericSymmetricEpsilonData F ψ ν.val ν.property π.representation
      σ.representation hπ hσ := by
  let := F.canonicalTopologicalData.topology
  exact (h p F ψ ν r t π σ hπ hσ e he).unique
    (genericSymmetricEpsilonData_isPadic F ψ ν.val ν.property π.representation
      σ.representation hπ hσ)

/-- Under the comparison, once a generic pair has some classification epsilon
factor, the classification and integral epsilon relations of the pair agree. -/
theorem isLanglandsPairEpsilonFactor_iff
    (h : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uV, uW})
    (hπ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ r π.representation)
    (hσ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ t σ.representation)
    (hex : ∃ e₀ : ℂˣ × ℤ, IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e₀)
    (e : ℂˣ × ℤ) :
    IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e ↔
      letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricEpsilonFactor F ψ ν.val π.representation σ.representation e := by
  obtain ⟨e₀, he₀⟩ := hex
  refine ⟨h p F ψ ν r t π σ hπ hσ e, fun he => ?_⟩
  have hee : e₀ = e := (h p F ψ ν r t π σ hπ hσ e₀ he₀).unique he
  exact hee ▸ he₀

/-- Combined with the published existence statement, the comparison at the
saturated universes makes the constructed integral epsilon data of a generic
pair a classification epsilon factor of the pair. -/
theorem isLanglandsPairEpsilonFactor_genericSymmetricEpsilonData
    (hex : LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW})
    (h : GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, max uF uV, max uF uW})
    (hπ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ r π.representation)
    (hσ : letI := F.canonicalTopologicalData.topology; IsGeneric ψ t σ.representation) :
    letI := F.canonicalTopologicalData.topology
    IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν.val π σ
      (genericSymmetricEpsilonData F ψ ν.val ν.property π.representation
        σ.representation hπ hσ) := by
  obtain ⟨e, he⟩ := hex p F ψ ν r t π σ hπ.1 hπ.2.1 hσ.1 hσ.2.1
  rw [← eq_genericSymmetricEpsilonData h hπ hσ he]
  exact he

end GenericLanglandsPairEpsilonFactorComparisonStatement

end Langlands.RankinSelberg
