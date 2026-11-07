import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Correspondence.RankOneAnalyticGaussEpsilon
import Langlands.Correspondence.RankOneAnalyticLFactor

/-! Separate actual pair L- and epsilon-factor compatibility in rank one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure GodementJacquet

universe uF uP uA uB uS

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩

/-- Uniqueness of the actual self-dual Haar measure identifies the two
independently constructed Gauss coefficients. -/
theorem tateEpsilonCoefficient_eq_rankOneArithmetic
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν) (χ : QuasiCharacter F) :
    Padic.tateEpsilonCoefficient F ν χ ψ = rankOneArithmeticEpsilonCoefficient F ψ χ := by
  apply Units.ext
  change PadicAbelian.deligneConstant F.canonicalTopologicalData χ ψ ν.measure =
    PadicAbelian.deligneConstant F.canonicalTopologicalData χ ψ
      (localSelfDualHaar F ψ).measure
  rw [eq_localSelfDualHaar F ψ ν hν]

/-- Every actual pair of rank-one Weil classes has a common full arithmetic
and automorphic epsilon certificate at every supplied self-dual measure. -/
theorem rankOneReciprocityEquiv_pairEpsilonCompatibility
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (hbase : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uS} F)
    (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    ∃ d : ℂˣ × ℤ,
      IsSupercuspidalPairEpsilonFactor F ψ ν
        (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
        (rankOneReciprocityEquiv.{uF, uP, uB} F e τ) d ∧
      IsArithmeticPairEpsilonFactor F eC ε hε ψ
        (weilPairClass F σ) (weilPairClass F τ) d.1 d.2 := by
  obtain ⟨χ, η, hσ, hτ, hAuto⟩ :=
    rankOneReciprocityEquiv_pairEpsilonGauss F ψ ν hν e σ τ
  have hArith := isArithmeticPairEpsilonFactor_rankOne_constructed F e eC hbase ε hε ψ χ η
  rw [← IsRankOneWeilCharacter.class_unique F hσ (rankOneWeilCharacterClass_spec F e χ),
    ← IsRankOneWeilCharacter.class_unique F hτ (rankOneWeilCharacterClass_spec F e η)]
    at hArith
  rw [tateEpsilonCoefficient_eq_rankOneArithmetic F ψ ν hν (χ * η)] at hAuto
  exact ⟨(_, _), hAuto, hArith⟩

/-- The complete rank-one case of separate pair-factor compatibility, including
actual self-dual measure existence and every such supplied measure. -/
def RankOnePairFactorCompatibilityStatement
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uS} F)
    (hε : NonabelianSystem.IsSystem F eC ε) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1),
    (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
    ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
      (∃ P : Polynomial ℂ,
        IsSupercuspidalPairLPolynomial F ψ ν
          (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
          (rankOneReciprocityEquiv.{uF, uP, uB} F e τ) P ∧
        arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) =
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)⁻¹) ∧
      ∃ d : ℂˣ × ℤ,
        IsSupercuspidalPairEpsilonFactor F ψ ν
          (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
          (rankOneReciprocityEquiv.{uF, uP, uB} F e τ) d ∧
        IsArithmeticPairEpsilonFactor F eC ε hε ψ
          (weilPairClass F σ) (weilPairClass F τ) d.1 d.2

theorem rankOnePairFactorCompatibilityStatement
    {e : ReciprocityCandidate F} (he : IsGeometricReciprocity F e)
    (eC : ReciprocityFamily F) (hbase : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uS} F)
    (hε : NonabelianSystem.IsSystem F eC ε) :
    RankOnePairFactorCompatibilityStatement.{uF, uP, uA, uB, uS} F e eC ε hε := by
  intro ψ σ τ
  refine ⟨⟨localSelfDualHaar F ψ, isSelfDual_localSelfDualHaar F ψ⟩, ?_⟩
  intro ν hν
  exact ⟨rankOneReciprocityEquiv_pairLCompatibility F ψ ν he σ τ,
    rankOneReciprocityEquiv_pairEpsilonCompatibility F e eC hbase ε hε ψ ν hν σ τ⟩

/-- Any two supplied families realizing the same rank-one reciprocity satisfy
the corresponding common arithmetic/automorphic epsilon comparison. -/
theorem SupercuspidalRankOneCompatibility.pairEpsilonCompatibility
    {e : ReciprocityCandidate F} (eC : ReciprocityFamily F)
    (hbase : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uS} F)
    (hε : NonabelianSystem.IsSystem F eC ε)
    {c : SupercuspidalMap.{uF, uP, uA} F}
    {d : SupercuspidalMap.{uF, uP, uB} F}
    (hc : SupercuspidalRankOneCompatibility F e c)
    (hd : SupercuspidalRankOneCompatibility F e d)
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    ∃ z : ℂˣ × ℤ,
      IsSupercuspidalPairEpsilonFactor F ψ ν (c 1 σ) (d 1 τ) z ∧
      IsArithmeticPairEpsilonFactor F eC ε hε ψ
        (weilPairClass F σ) (weilPairClass F τ) z.1 z.2 := by
  rw [(supercuspidalRankOneCompatibility_iff_eq F e c).mp hc,
    (supercuspidalRankOneCompatibility_iff_eq F e d).mp hd]
  exact rankOneReciprocityEquiv_pairEpsilonCompatibility F e eC hbase ε hε ψ ν hν σ τ

end Langlands.Correspondence
