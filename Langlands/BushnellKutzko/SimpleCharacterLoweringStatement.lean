import Langlands.BushnellKutzko.SimpleCharacterPairs

/-! # Lowering the character level (BK93 (3.5.9), printed p. 121) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- If the depth-`m` character sets agree, so do the groups `H^m`, and an
equivalent first stratum can be chosen with the same depth-`m−1` characters
as the second. -/
def SimpleCharacterLoweringStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ), 1 ≤ m →
    ∀ (S T : SimpleStratumAt L n m),
      simpleCharacterPairs ψF S.1 m = simpleCharacterPairs ψF T.1 m →
      (∀ (q : S.1.DefiningSequenceChoice) (q' : T.1.DefiningSequenceChoice),
        simpleHGroup L n S.1.b q.tail m = simpleHGroup L n T.1.b q'.tail m) ∧
      ∃ S' : SimpleStratumAt L n m,
        S'.1.Equivalent S.1 ∧
        simpleCharacterPairs ψF S'.1 (m - 1) = simpleCharacterPairs ψF T.1 (m - 1)

end Langlands.BushnellKutzko
