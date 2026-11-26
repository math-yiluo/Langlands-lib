import Langlands.BushnellKutzko.SimpleCharacterPairs
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # Invariants from a common simple character (BK93 (3.5.1), printed p. 117) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- Two simple strata on the same order and at the same levels that share a
simple character have the same critical exponent, ramification index and
residue degree. -/
def SimpleCharacterInvariantsStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ) (S T : SimpleStratumAt L n m),
      (simpleCharacterPairs ψF S.1 m ∩ simpleCharacterPairs ψF T.1 m).Nonempty →
      criticalExponent L S.1.b = criticalExponent L T.1.b ∧
      elementRamificationIndex F S.1.b = elementRamificationIndex F T.1.b ∧
      elementResidueDegree F S.1.b = elementResidueDegree F T.1.b

end Langlands.BushnellKutzko
