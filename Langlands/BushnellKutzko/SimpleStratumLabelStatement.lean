import Langlands.BushnellKutzko.ElementFieldInvariants
import Langlands.BushnellKutzko.Labels

/-! # Labels for simple strata in a principal order -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- The upper-bound direction of BK94 (1.14), printed p. 116, for a
principal hereditary order. There is a labeling of the simple strata
with fixed order and levels. Equal labels imply order-unit conjugacy up
to equivalence, and each label determines both field invariants. -/
def SimpleStratumLabelStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : LatticeChain 𝒪[F] F V) (m n : ℤ),
    1 ≤ Module.finrank F V → L.IsPrincipal → 0 ≤ m → m < n →
    let SimpleStrata := {S : Stratum 𝒪[F] F V //
      S.chain = L ∧ S.n = n ∧ S.r = m ∧ S.IsSimple}
    ∃ ρ : SimpleStrata →
        ↥(labelSet m.toNat n.toNat L.period (Module.finrank F V / L.period)
          (Nat.card 𝓀[F])),
      (∀ S T : SimpleStrata, ρ S = ρ T →
        ∃ u ∈ L.unitFiltration 0,
          (↑(u⁻¹) : Module.End F V) * S.1.b * (u : Module.End F V) ∈ T.1.coset) ∧
      (∀ S : SimpleStrata,
        (ρ S).1.d = elementResidueDegree F S.1.b ∧
        elementRamificationIndex F S.1.b * (ρ S).1.e = L.period)

end Langlands.BushnellKutzko
