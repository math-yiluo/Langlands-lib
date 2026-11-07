import Langlands.LocalFactor.CommonClosureRankOneEpsilon
import Langlands.Correspondence.ArithmeticEpsilonDirectSum
import Langlands.Correspondence.RankOneReciprocityBijection
import Langlands.Correspondence.UnramifiedReciprocityBridge

/-! # Arithmetic epsilon certificates of actual rank-one Weil classes -/

noncomputable section

universe uF uP uV

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneArithmeticEpsilonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- Restriction of an actual continuous Weil character to the bottom subgroup. -/
def baseRestrictedWeilCharacter (χ : Weil.Local.localWeilGroup F →ₜ* ℂˣ) :
    weilSubgroup F (baseExtension F) →ₜ* ℂˣ :=
  χ.comp
    { toMonoidHom := (weilSubgroup F (baseExtension F)).subtype
      continuous_toFun := continuous_subtype_val }

/-- The actual restricted character pair can be moved to the system's
independent carrier universe through the scalar line. -/
def rankOneBaseCharacterPairEquiv (χ : Weil.Local.localWeilGroup F →ₜ* ℂˣ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (WeilDeligneRepresentation.zeroMonodromy (Weil.Local.localNormCharacter F).toMonoidHom
          (FiniteRepresentation.characterLine.{uF, uP} χ.toMonoidHom)))
      (characterPair.{uF, uV} F (baseExtension F) (baseRestrictedWeilCharacter F χ)) :=
  WeilDeligneRepresentation.zeroMonodromyCongr _
    ((FiniteRepresentation.characterLineEquiv.{uF, uP}
      (baseRestrictedWeilCharacter F χ).toMonoidHom).trans
      (FiniteRepresentation.characterLineEquiv.{uF, max uF uV}
        (baseRestrictedWeilCharacter F χ).toMonoidHom).symm)

/-- The explicit bottom character pair is a genuine restriction datum of the
specified actual rank-one Weil class. -/
theorem isBaseRestriction_rankOneWeilCharacterClass (e : ReciprocityCandidate F)
    (χ : QuasiCharacter F) :
    IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (characterPair.{uF, uV} F (baseExtension F)
        (baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ))) := by
  refine ⟨WeilDeligneRepresentation.zeroMonodromy
    (Weil.Local.localNormCharacter F).toMonoidHom
    (FiniteRepresentation.characterLine.{uF, uP}
      (RankOne.weilCharacter F e χ).toMonoidHom), rfl, ?_⟩
  exact ⟨rankOneBaseCharacterPairEquiv F (RankOne.weilCharacter F e χ)⟩

/-- Every bottom restriction of the actual rank-one class is genuinely
equivalent to its explicit character pair. -/
theorem IsBaseRestriction.nonempty_equiv_rankOneWeilCharacterClass
    (e : ReciprocityCandidate F) (χ : QuasiCharacter F)
    {A : Pair.{uF, uV} F (baseExtension F)}
    (hA : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ)) A) :
    Nonempty (WeilDeligneRepresentation.Equiv A
      (characterPair.{uF, uV} F (baseExtension F)
        (baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ)))) := by
  obtain ⟨f⟩ := IsBaseRestriction.nonempty_equiv F
    (A := WeilDeligneRepresentation.zeroMonodromy
      (Weil.Local.localNormCharacter F).toMonoidHom
      (FiniteRepresentation.characterLine.{uF, uP}
        (RankOne.weilCharacter F e χ).toMonoidHom)) rfl hA
  exact ⟨f.symm.trans (rankOneBaseCharacterPairEquiv F (RankOne.weilCharacter F e χ))⟩

/-- The full conditional pair epsilon value for arbitrary actual bottom
restrictions of the specified rank-one classes. -/
theorem conditionalPairEpsilonValue_of_rankOneBaseRestriction
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (χ η : QuasiCharacter F)
    (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    {A B : Pair.{uF, uV} F (baseExtension F)}
    (hA : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ)) A)
    (hB : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) B)
    (hAc : A.toFiniteRepresentation.IsContinuous) (hBc : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ) :
    (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
      A B hAc hBc Φ s : ℂ) =
      (fieldData F (baseExtension F)).abelianEpsilonExpression
        (characterDescentEquiv F eC (baseExtension F)
          (CommonClosureSpectral.character F (baseExtension F) s *
            (baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ) *
              baseRestrictedWeilCharacter F (RankOne.weilCharacter F e η)))) ψ' μ := by
  obtain ⟨f⟩ := hA.nonempty_equiv_rankOneWeilCharacterClass F e χ
  obtain ⟨g⟩ := hB.nonempty_equiv_rankOneWeilCharacterClass F e η
  exact CommonClosureGamma.conditionalPairEpsilonValue_of_equiv_characterPair
    F eC ε hε (baseExtension F) ψ' μ hAc hBc _ _ f g Φ s

/-- The existing full arithmetic certificate is exactly an abelian identity,
with transported-character, self-dual-measure and Frobenius existence retained. -/
theorem isArithmeticPairEpsilonFactor_rankOneWeilCharacterClass_iff
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (χ η : QuasiCharacter F) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) c m ↔
      (∃ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F)),
        IsBaseCharacter F ψ ψ' ∧ CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ) ∧
      Nonempty (GeometricFrobenius F (baseExtension F)) ∧
      ∀ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F)),
        IsBaseCharacter F ψ ψ' →
        CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ →
        ∀ s : ℂ,
          (fieldData F (baseExtension F)).abelianEpsilonExpression
            (characterDescentEquiv F eC (baseExtension F)
              (CommonClosureSpectral.character F (baseExtension F) s *
                (baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ) *
                  baseRestrictedWeilCharacter F (RankOne.weilCharacter F e η)))) ψ' μ =
            RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s := by
  let χ' := baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ)
  let η' := baseRestrictedWeilCharacter F (RankOne.weilCharacter F e η)
  let A := characterPair.{uF, uV} F (baseExtension F) χ'
  let B := characterPair.{uF, uV} F (baseExtension F) η'
  have hA : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ)) A :=
    isBaseRestriction_rankOneWeilCharacterClass F e χ
  have hB : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) B :=
    isBaseRestriction_rankOneWeilCharacterClass F e η
  have hAc : A.toFiniteRepresentation.IsContinuous := characterPair_isContinuous F _ χ'
  have hBc : B.toFiniteRepresentation.IsContinuous := characterPair_isContinuous F _ η'
  constructor
  · intro h
    refine ⟨?_, h.2.1, ?_⟩
    · obtain ⟨ψ', μ, C, D, hd, _, _⟩ := h.1
      exact ⟨ψ', μ, hd.1, hd.2.1⟩
    · intro ψ' μ hψ hμ s
      obtain ⟨Φ⟩ := h.2.1
      have hv := h.2.2 ψ' μ A B ⟨hψ, hμ, hA, hB⟩ hAc hBc Φ s
      rw [conditionalPairEpsilonValue_of_rankOneBaseRestriction
        F e eC ε hε χ η ψ' μ hA hB hAc hBc Φ s] at hv
      exact hv
  · rintro ⟨⟨ψ', μ, hψ, hμ⟩, hΦ, hv⟩
    refine ⟨⟨ψ', μ, A, B, ⟨hψ, hμ, hA, hB⟩, hAc, hBc⟩, hΦ, ?_⟩
    intro ψ'' μ' C D hd hC hD Φ s
    rw [conditionalPairEpsilonValue_of_rankOneBaseRestriction
      F e eC ε hε χ η ψ'' μ' hd.2.2.1 hd.2.2.2 hC hD Φ s]
    exact hv ψ'' μ' hd.1 hd.2.1 s

end Langlands.Correspondence
