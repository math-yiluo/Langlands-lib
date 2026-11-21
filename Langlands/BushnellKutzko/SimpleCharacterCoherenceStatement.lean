import Langlands.BushnellKutzko.SimpleCharacters

/-! # Coherence (BK93 (3.5.8), printed p. 120; U7) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (3.5.8), U7.** If the character groups have the same domain and
share one character, their full sets of simple characters are equal. -/
def SimpleCharacterCoherenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S T : Stratum 𝒪[F] F V) (m : ℕ), T.chain.order = S.chain.order → T.n = S.n →
      S.r = m → T.r = m → S.IsSimple → T.IsSimple →
      ∀ (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice),
        let G := (Module.End F V)ˣ
        let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
        let H' := simpleHGroup T.chain T.n T.b q'.tail (m + 1)
        let C := simpleCharacters ψF S.chain S.n S.b q.tail m
        let C' := simpleCharacters ψF T.chain T.n T.b q'.tail m
        ∀ h : H = H',
          let C₁ := Eq.ndrec (motive := fun K : Subgroup G => Set (K →* ℂˣ)) C h
          (C₁ ∩ C').Nonempty → C₁ = C'

end Langlands.BushnellKutzko
