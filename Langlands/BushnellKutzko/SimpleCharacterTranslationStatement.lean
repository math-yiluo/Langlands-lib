import Langlands.BushnellKutzko.SimpleCharacterPairs

/-! # The Translation Principle (BK94 (2.11), printed p. 123) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- Equal sets of character pairs at depth `m+1` allow a simple lift of the
first stratum at depth `m` to be matched by a simple lift of the second. -/
def SimpleCharacterTranslationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ), (m : ℤ) + 1 < n →
    ∀ (T₁ T₂ : SimpleStratumAt L n ((m : ℤ) + 1)) (S₁ : SimpleStratumAt L n m),
      simpleCharacterPairs ψF T₁.1 (m + 1) = simpleCharacterPairs ψF T₂.1 (m + 1) →
      S₁.1.b - T₁.1.b ∈ L.endFiltration (-((m : ℤ) + 1)) →
      ∃ S₂ : SimpleStratumAt L n m,
        S₂.1.b - T₂.1.b ∈ L.endFiltration (-((m : ℤ) + 1)) ∧
        simpleCharacterPairs ψF S₂.1 m = simpleCharacterPairs ψF S₁.1 m

end Langlands.BushnellKutzko
