import Langlands.BushnellKutzko.CharacterPairConjugation
import Langlands.BushnellKutzko.SimpleTypesOverCharacter
import Langlands.BushnellKutzko.SplittingBasis

/-! # Transport of simple type data and conjugacy of principal orders -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uW

/-- Conjugation transports both kinds of simple type data and their periods.
The period of a principal order divides the dimension, and principal orders
of equal period are conjugate. -/
def SimpleTypeTransportStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    1 ≤ Module.finrank F V →
    let G := (Module.End F V)ˣ
    let Lattice := LatticeChain 𝒪[F] F V
    let S₀ := Stratum 𝒪[F] F V
    (∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (g : G)
        (J : Subgroup G) (ρ : Representation ℂ J W),
      let gLin := LinearMap.GeneralLinearGroup.toLinearEquiv g
      (∀ (S : S₀) (q : S.DefiningSequenceChoice) (e : ℕ)
          (θ : simpleHGroup S.chain S.n S.b q.tail 1 →* ℂˣ),
        IsSimpleTypeDataOver ψF S q e θ ρ →
        ∃ (T : S₀) (q' : T.DefiningSequenceChoice)
          (θ' : simpleHGroup T.chain T.n T.b q'.tail 1 →* ℂˣ),
          T.chain = S.chain.linearEquivMap gLin ∧ T.n = S.n ∧ T.r = S.r ∧
          T.b = gLin.conjRingEquiv S.b ∧
          (⟨_, θ'⟩ : CharacterPair G) = CharacterPair.conj g⁻¹ ⟨_, θ⟩ ∧
          IsSimpleTypeDataOver ψF T q' e θ' (conjRepresentation g ρ)) ∧
      (∀ (L : Lattice) (e : ℕ), IsLevelZeroSimpleTypeData L e ρ →
        (L.linearEquivMap gLin).period = L.period ∧
        IsLevelZeroSimpleTypeData (L.linearEquivMap gLin) e (conjRepresentation g ρ))) ∧
    (∀ L : Lattice, IsPrincipalOrder L.order →
      L.period ∣ Module.finrank F V) ∧
    (∀ L₁ L₂ : Lattice, IsPrincipalOrder L₁.order → IsPrincipalOrder L₂.order →
      L₁.period = L₂.period →
      ∃ g : G, (L₁.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g)).order = L₂.order)

end Langlands.BushnellKutzko
