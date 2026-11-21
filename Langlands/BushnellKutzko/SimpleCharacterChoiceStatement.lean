import Langlands.BushnellKutzko.SimpleCharacters

/-! # Choice independence and change of equivalent stratum (BK93 (3.3.20), p. 113; U4) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uG

/-- Character values obtained by twisting members of a set of characters and
comparing on the entire target domain. Used only with equal domains in U4. -/
def characterSetTwist {G : Type uG} [Group G] {H₁ : Subgroup G} (H₂ : Subgroup G)
    (C : Set (H₁ →* ℂˣ)) (twist : G → ℂ) : Set (H₂ →* ℂˣ) :=
  {θ₂ | ∃ θ₁ ∈ C, characterAgreesOn H₂ θ₂ θ₁ twist}

/-- **BK93 (3.3.20), U4.** Independence of defining sequences and the exact
character-set twist for equivalent simple strata. -/
def SimpleCharacterChoiceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    let H := fun m : ℕ => simpleHGroup S.chain S.n S.b q.tail (m + 1)
    let C := simpleCharacters ψF S.chain S.n S.b q.tail
    (∀ (q' : S.DefiningSequenceChoice) (m : ℕ), (m : ℤ) < S.n →
      let H' := simpleHGroup S.chain S.n S.b q'.tail (m + 1)
      H m = H' ∧ simpleCharacters ψF S.chain S.n S.b q'.tail m =
        characterSetTwist H' (C m) (fun _ => 1)) ∧
    ∀ T : Stratum 𝒪[F] F V,
      T.chain.order = S.chain.order → T.n = S.n → T.IsSimple →
      0 ≤ T.r → (T.r : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
      T.b - S.b ∈ S.chain.endFiltration (-T.r) →
      ∀ (q' : T.DefiningSequenceChoice) (m : ℕ),
        T.r / 2 ≤ (m : ℤ) → (m : ℤ) < S.n →
        ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
        let H' := simpleHGroup T.chain T.n T.b q'.tail (m + 1)
        H m = H' ∧ simpleCharacters ψF T.chain T.n T.b q'.tail m =
          characterSetTwist H' (C m) (elementCharacter (traceCharacter ψF) (T.b - S.b))

end Langlands.BushnellKutzko
