import Langlands.BushnellKutzko.SimpleCharacterPairs

/-! # Covering simple-character classes by simple strata (BK94 (2.3), printed p. 119) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- A choice of one character pair per simple stratum induces a surjection
from the stratum classes to the simple-character conjugacy classes. -/
def SimpleCharacterClassCoverStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ), (m : ℤ) < n →
    let G := (Module.End F V)ˣ
    let U := L.unitFiltration 0
    ∃ Φ : SimpleStratumAt L n m → CharacterPair G,
      (∀ S, Φ S ∈ simpleCharacterPairs ψF S.1 m) ∧
      (∀ (S T : SimpleStratumAt L n m) (u : U),
        let x : G := u
        T.1.b - ((↑x⁻¹ : Module.End F V) * S.1.b * (↑x : Module.End F V)) ∈
          L.endFiltration (-(m : ℤ)) →
        CharacterPair.AreConjugateBy U (Φ S) (Φ T)) ∧
      (∀ P ∈ simpleCharacterPairsAt ψF L n m,
        ∃ S : SimpleStratumAt L n m, CharacterPair.AreConjugateBy U (Φ S) P)

end Langlands.BushnellKutzko
