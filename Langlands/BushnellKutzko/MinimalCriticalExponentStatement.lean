import Langlands.BushnellKutzko.MinimalElement
import Langlands.BushnellKutzko.AdjointCriticalExponent

/-! # Critical exponent and minimality (BK93 (1.4.15), p. 41; T3) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uE

/-- **BK93 (1.4.15), printed p. 41 (T3).** For `E = F[β] ≠ F`
normalizing the order, `v_𝔄(β) ≤ k₀`, with equality exactly at minimal elements. -/
def MinimalCriticalExponentStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (𝓛 : LatticeChain 𝒪[F] F V) (β : E),
    Algebra.adjoin F ({β} : Set E) = ⊤ →
    (¬ ∃ a : F, algebraMap F E a = β) →
    (∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) →
    let b := subfieldEmbedding F E V β
    ∃ k₀ : ℤ, criticalExponent 𝓛 b = (k₀ : WithBot ℤ) ∧
      𝓛.valuation b ≤ (k₀ : WithTop ℤ) ∧
      (𝓛.valuation b = (k₀ : WithTop ℤ) ↔ IsMinimalOver F E β)

end Langlands.BushnellKutzko
