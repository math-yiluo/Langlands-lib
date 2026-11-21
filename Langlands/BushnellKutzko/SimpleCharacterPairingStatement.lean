import Langlands.BushnellKutzko.SimpleCharacters

/-! # The commutator pairing (BK93 (3.4.1), printed p. 115; U6) -/

open ValuativeRel
open scoped commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (3.4.1), U6.** The evaluated commutator descends to a
nondegenerate alternating bimultiplicative form on `J^m/H^m`, where `m=i+1`. -/
def SimpleCharacterPairingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ i : ℕ, let m := i + 1
      (m : ℤ) ≤ S.n → ((m : ℤ) : WithTop ℤ) ≤ simpleCriticalDepth S.chain S.b →
      ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i,
        let G := (Module.End F V)ˣ
        let H := simpleHGroup S.chain S.n S.b q.tail m
        let J := simpleJGroup S.chain S.n S.b q.tail m
        let N := H.comap J.subtype
        H ≤ J ∧ ∃ hN : N.Normal,
          letI := hN
          let Q := J ⧸ N
          let π := QuotientGroup.mk' N
          ∃ B : Q →* (Q →* ℂˣ),
            (∀ x y : J, ∃ h : ⁅(x : G), (y : G)⁆ ∈ H,
              B (π x) (π y) = θ ⟨_, h⟩) ∧
            (∀ x : Q, B x x = 1) ∧
            (∀ x : Q, (∀ y : Q, B x y = 1) → x = 1)

end Langlands.BushnellKutzko
