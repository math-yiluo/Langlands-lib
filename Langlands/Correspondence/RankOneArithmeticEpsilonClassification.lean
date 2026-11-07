import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Correspondence.SupercuspidalEpsilonComparison

/-! # Exact arithmetic epsilon data on arbitrary rank-one Weil classes -/

noncomputable section

universe uF uP uV uW

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance arithmeticEpsilonClassTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The actual coefficient and conductor exponent for two arbitrary rank-one
Weil classes, using their unique descended field characters. -/
def rankOneArithmeticEpsilonData (e : ReciprocityCandidate F)
    (ψ : NontrivialAdditiveCharacter F)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) : ℂˣ × ℤ :=
  let χ := (rankOneWeilCharacterEquiv F e).symm σ
  let η := (rankOneWeilCharacterEquiv F e).symm τ
  (rankOneArithmeticEpsilonCoefficient F ψ (χ * η),
    PadicAbelian.epsilonExponent F.canonicalTopologicalData (χ * η) ψ)

/-- The constructed data satisfy the complete original arithmetic certificate
on every actual rank-one Weil-class pair. -/
theorem rankOneArithmeticEpsilonData_spec
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ (weilPairClass F σ) (weilPairClass F τ)
      (rankOneArithmeticEpsilonData F e ψ σ τ).1
      (rankOneArithmeticEpsilonData F e ψ σ τ).2 := by
  have hσ : rankOneWeilCharacterClass F e ((rankOneWeilCharacterEquiv F e).symm σ) = σ :=
    (rankOneWeilCharacterEquiv F e).apply_symm_apply σ
  have hτ : rankOneWeilCharacterClass F e ((rankOneWeilCharacterEquiv F e).symm τ) = τ :=
    (rankOneWeilCharacterEquiv F e).apply_symm_apply τ
  convert isArithmeticPairEpsilonFactor_rankOne_constructed F e eC h ε hε ψ
    ((rankOneWeilCharacterEquiv F e).symm σ) ((rankOneWeilCharacterEquiv F e).symm τ) using 1 <;>
    simp only [hσ, hτ, rankOneArithmeticEpsilonData]

/-- The full original certificate holds exactly for the constructed coefficient
and exponent; all existence clauses are discharged by the specification theorem. -/
theorem isArithmeticPairEpsilonFactor_rankOne_iff_eq_data
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ (weilPairClass F σ) (weilPairClass F τ) c m ↔
      (c, m) = rankOneArithmeticEpsilonData F e ψ σ τ := by
  have hs := rankOneArithmeticEpsilonData_spec F e eC h ε hε ψ σ τ
  constructor
  · intro hc
    exact Prod.ext (hc.unique F hs).1 (hc.unique F hs).2
  · intro heq
    have hc := congrArg Prod.fst heq
    have hm := congrArg Prod.snd heq
    change c = _ at hc
    change m = _ at hm
    simpa only [hc, hm] using hs

/-- Rank-one arithmetic certificates are independent of the supplied compatible
common-closure systems, without a general nonabelian-system uniqueness premise. -/
theorem rankOneArithmeticPairEpsilonComparison
    (e : ReciprocityCandidate F) (eC₁ eC₂ : ReciprocityFamily F)
    (h₁ : IsBaseReciprocity F e eC₁) (h₂ : IsBaseReciprocity F e eC₂)
    (ε₁ : NonabelianSystem.Assignment.{uF, uV} F)
    (hε₁ : NonabelianSystem.IsSystem F eC₁ ε₁)
    (ε₂ : NonabelianSystem.Assignment.{uF, uW} F)
    (hε₂ : NonabelianSystem.IsSystem F eC₂ ε₂)
    (ψ : NontrivialAdditiveCharacter F)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC₁ ε₁ hε₁ ψ (weilPairClass F σ) (weilPairClass F τ) c m ↔
      IsArithmeticPairEpsilonFactor F eC₂ ε₂ hε₂ ψ (weilPairClass F σ) (weilPairClass F τ) c m := by
  rw [isArithmeticPairEpsilonFactor_rankOne_iff_eq_data F e eC₁ h₁ ε₁ hε₁ ψ σ τ c m,
    isArithmeticPairEpsilonFactor_rankOne_iff_eq_data F e eC₂ h₂ ε₂ hε₂ ψ σ τ c m]

end Langlands.Correspondence
