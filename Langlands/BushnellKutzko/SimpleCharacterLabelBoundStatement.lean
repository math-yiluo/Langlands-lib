import Langlands.BushnellKutzko.SimpleCharacterPairs
import Langlands.BushnellKutzko.ElementFieldInvariants
import Langlands.BushnellKutzko.Labels

/-! # The label bound for simple-character classes (BK94 (2.5), printed p. 120) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- Simple characters in a principal order admit labels whose fibers lie in
single conjugacy classes and whose invariants record `e(F[β]|F)` and `f(F[β]|F)`. -/
def SimpleCharacterLabelBoundStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    1 ≤ Module.finrank F V →
    ∀ (L : LatticeChain 𝒪[F] F V), L.IsPrincipal →
    ∀ (n : ℤ) (m : ℕ), (m : ℤ) < n →
    let S := simpleCharacterPairsAt ψF L n m
    let P := labelSet m n.toNat L.period (Module.finrank F V / L.period) (Nat.card 𝓀[F])
    ∃ σ : S → P,
      (∀ P₁ P₂ : S, σ P₁ = σ P₂ →
        CharacterPair.AreConjugateBy (L.unitFiltration 0) P₁.1 P₂.1) ∧
      (∀ (T : SimpleStratumAt L n m) (Q : S), Q.1 ∈ simpleCharacterPairs ψF T.1 m →
        (σ Q).1.d = elementResidueDegree F T.1.b ∧
        elementRamificationIndex F T.1.b * (σ Q).1.e = L.period)

end Langlands.BushnellKutzko
