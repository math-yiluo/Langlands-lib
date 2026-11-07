import Langlands.Correspondence.RankOneEpsilonFieldTransport
import Langlands.LocalFactor.Abelian.NormalizedTwist

/-! # Full rank-one arithmetic pair epsilon in the fixed-Haar spectral convention -/

noncomputable section

universe uF uP uV

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance spectralEpsilonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance spectralEpsilonMeasurable : MeasurableSpace F.Carrier := borel F.Carrier

/-- The full arithmetic pair epsilon value is the actual fixed-Haar abelian
spectral expression for the original product character, at the same parameter. -/
theorem conditionalPairEpsilonValue_eq_abelianSpectral
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (χ η : QuasiCharacter F) (ψ : NontrivialAdditiveCharacter F)
    (ψ' : AdditiveCharacter F (baseExtension F)) (hψ : IsBaseCharacter F ψ ψ')
    (μ : HaarMeasure F (baseExtension F))
    {A B : Pair.{uF, uV} F (baseExtension F)}
    (hA : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ)) A)
    (hB : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) B)
    (hAc : A.toFiniteRepresentation.IsContinuous) (hBc : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ) :
    (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
      A B hAc hBc Φ s : ℂ) =
      PadicAbelian.epsilon F.canonicalTopologicalData (χ * η) ψ
        ((baseFieldHaarMeasureEquiv F).symm μ).measure s := by
  rw [conditionalPairEpsilonValue_on_baseField
    F e eC h ε hε χ η ψ ψ' hψ μ hA hB hAc hBc Φ s,
    PadicAbelian.abelianEpsilonExpression_normalizedAbsPower_mul]

/-- The exact rank-one arithmetic certificate in the actual abelian spectral
convention, keeping all harmonic existence and universal clauses. -/
theorem isArithmeticPairEpsilonFactor_rankOne_spectral_iff
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (χ η : QuasiCharacter F) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) c m ↔
      (∃ μ : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ μ) ∧
      Nonempty (GeometricFrobenius F (baseExtension F)) ∧
      ∀ μ : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ μ → ∀ s : ℂ,
        PadicAbelian.epsilon F.canonicalTopologicalData (χ * η) ψ μ.measure s =
          RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s := by
  rw [isArithmeticPairEpsilonFactor_rankOne_on_baseField_iff F e eC h ε hε ψ χ η c m]
  simp_rw [PadicAbelian.abelianEpsilonExpression_normalizedAbsPower_mul]

end Langlands.Correspondence
