import Langlands.BushnellKutzko.CharacterPairConjugation
import Langlands.BushnellKutzko.SimpleTypesOverCharacter

/-! # Conjugate simple characters and the types over them (BK94 (3.4)) -/

open ValuativeRel Langlands.Group.RelativeWeyl

namespace Langlands.BushnellKutzko

universe uF uV uW

/-- Conjugating a simple character by an order unit conjugates `J` and
transports the simple types over that character. -/
def SimpleTypesOverCharacterConjugationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    1 ≤ Module.finrank F V →
    ∀ (S₁ S₂ : Stratum 𝒪[F] F V) (q₁ : S₁.DefiningSequenceChoice) (q₂ : S₂.DefiningSequenceChoice),
    S₁.IsSimple → S₂.IsSimple → S₁.r = 0 → S₂.r = 0 → S₁.n = S₂.n →
    S₁.chain.order = S₂.chain.order → IsPrincipalOrder S₁.chain.order →
    ∀ θ₁ ∈ simpleCharacters ψF S₁.chain S₁.n S₁.b q₁.tail 0,
    ∀ θ₂ ∈ simpleCharacters ψF S₂.chain S₂.n S₂.b q₂.tail 0,
    let G := (Module.End F V)ˣ
    let J₁ := simpleJ S₁.chain S₁.n S₁.b q₁.tail
    let J₂ := simpleJ S₂.chain S₂.n S₂.b q₂.tail
    ∀ u : S₁.chain.unitFiltration 0,
    (⟨_, θ₂⟩ : CharacterPair G) = CharacterPair.conj (u : G) ⟨_, θ₁⟩ →
    ∃ hJ : J₂ = conjugateSubgroup (u : G)⁻¹ J₁,
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ J₁ W),
      IsSimpleTypeOver ψF S₁ q₁ θ₁ ρ →
      IsSimpleTypeOver ψF S₂ q₂ θ₂
        ((conjRepresentation (u : G)⁻¹ ρ).comp (MulEquiv.subgroupCongr hJ).toMonoidHom)

end Langlands.BushnellKutzko
