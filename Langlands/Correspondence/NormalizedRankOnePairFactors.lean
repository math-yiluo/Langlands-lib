import Langlands.Correspondence.BaseGeometricResidue
import Langlands.Correspondence.RankOnePairFactorCompatibility

/-! # Rank-one pair factors from a supplied normalized reciprocity family -/

noncomputable section

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure GodementJacquet

universe uF uP uA uB uS

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩

/-- A supplied normalized family supplies the geometric premise for every
compatible base candidate's separate rank-one pair factors. -/
theorem rankOnePairFactorCompatibility_of_normalized
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (heC : NormalizedReciprocity F eC) (hbase : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uS} F)
    (hε : NonabelianSystem.IsSystem F eC ε) :
    RankOnePairFactorCompatibilityStatement.{uF, uP, uA, uB, uS} F e eC ε hε :=
  rankOnePairFactorCompatibilityStatement F
    (isGeometricReciprocity_of_isBaseReciprocity F e eC hbase heC)
    eC hbase ε hε

/-- Separate rank-one pair L- and epsilon-factor compatibility for the explicit
base candidate of every supplied normalized family and supplied system. -/
def NormalizedRankOnePairFactorCompatibilityStatement : Prop :=
  ∀ (eC : ReciprocityFamily F), NormalizedReciprocity F eC →
    ∀ (ε : NonabelianSystem.Assignment.{uF, uS} F)
      (hε : NonabelianSystem.IsSystem F eC ε),
      RankOnePairFactorCompatibilityStatement.{uF, uP, uA, uB, uS} F
        (baseReciprocityCandidate F eC) eC ε hε

theorem normalizedRankOnePairFactorCompatibilityProof :
    NormalizedRankOnePairFactorCompatibilityStatement.{uF, uP, uA, uB, uS} F := by
  intro eC heC ε hε
  exact rankOnePairFactorCompatibility_of_normalized F
    (baseReciprocityCandidate F eC) eC heC
    (baseReciprocityCandidate_spec F eC) ε hε

/-- The complete separate pair-factor conclusion also holds for any two
supplied maps realizing the compatible rank-one reciprocity. -/
theorem SupercuspidalRankOneCompatibility.pairFactorCompatibility_of_normalized
    {e : ReciprocityCandidate F} (eC : ReciprocityFamily F)
    (heC : NormalizedReciprocity F eC) (hbase : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uS} F)
    (hε : NonabelianSystem.IsSystem F eC ε)
    {c : SupercuspidalMap.{uF, uP, uA} F}
    {d : SupercuspidalMap.{uF, uP, uB} F}
    (hc : SupercuspidalRankOneCompatibility F e c)
    (hd : SupercuspidalRankOneCompatibility F e d)
    (ψ : NontrivialAdditiveCharacter F)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
    ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
      (∃ P : Polynomial ℂ,
        IsSupercuspidalPairLPolynomial F ψ ν (c 1 σ) (d 1 τ) P ∧
        arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) =
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)⁻¹) ∧
      ∃ z : ℂˣ × ℤ,
        IsSupercuspidalPairEpsilonFactor F ψ ν (c 1 σ) (d 1 τ) z ∧
        IsArithmeticPairEpsilonFactor F eC ε hε ψ
          (weilPairClass F σ) (weilPairClass F τ) z.1 z.2 := by
  rw [(supercuspidalRankOneCompatibility_iff_eq F e c).mp hc,
    (supercuspidalRankOneCompatibility_iff_eq F e d).mp hd]
  exact rankOnePairFactorCompatibility_of_normalized F e eC heC hbase ε hε ψ σ τ

end Langlands.Correspondence
