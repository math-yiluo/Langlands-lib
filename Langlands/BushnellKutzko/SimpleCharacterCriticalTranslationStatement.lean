import Langlands.BushnellKutzko.SimpleCharacterPairs

/-! # Critical translation of a simple refinement (BK94 (5.3)–(5.6), printed pp. 132–133) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- Let `[𝔄,n,m+1,γ₁]` and `[𝔄,n,m+1,γ₂]` be simple strata with the same
depth-`m` character pairs. If `γ₁ + c`, with `c ∈ 𝔓^{−(m+1)}`, is simple at
level `m` with critical exponent `−(m+1)`, then `[𝔄,n,m,γ₂ + c]` is equivalent
to a simple stratum. -/
def SimpleCharacterCriticalTranslationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (m : ℕ)
      (T₁ T₂ : SimpleStratumAt L n ((m : ℤ) + 1)) (S₁ : SimpleStratumAt L n m),
      simpleCharacterPairs ψF T₁.1 m = simpleCharacterPairs ψF T₂.1 m →
      S₁.1.b - T₁.1.b ∈ L.endFiltration (-((m : ℤ) + 1)) →
      criticalExponent L S₁.1.b = ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ) →
      ∃ S₂ : SimpleStratumAt L n m,
        S₂.1.b - (T₂.1.b + (S₁.1.b - T₁.1.b)) ∈ L.endFiltration (-(m : ℤ))

end Langlands.BushnellKutzko
