import Langlands.BushnellKutzko.SimpleCharacters
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Transfer in one endomorphism algebra (BK93 (3.6.1), printed p. 127; U8) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (3.6.1), U8.** At the same normalized depth, a simple character
has a unique transfer agreeing with it on the intersection of the two domains. -/
def SimpleCharacterTransferStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S T : Stratum 𝒪[F] F V) (m₁ m₂ : ℕ), S.b = T.b →
      S.r = m₁ → T.r = m₂ → S.IsSimple → T.IsSimple →
      ∀ (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice),
        let e := elementRamificationIndex F S.b
        let e₁ := S.chain.period / e
        let e₂ := T.chain.period / e
        m₁ / e₁ = m₂ / e₂ →
        let H₁ := simpleHGroup S.chain S.n S.b q.tail (m₁ + 1)
        let H₂ := simpleHGroup T.chain T.n T.b q'.tail (m₂ + 1)
        ∀ θ₁ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m₁,
          ∃! θ₂, θ₂ ∈ simpleCharacters ψF T.chain T.n T.b q'.tail m₂ ∧
            characterAgreesOn (H₁ ⊓ H₂) θ₁ θ₂ (fun _ => 1)

end Langlands.BushnellKutzko
