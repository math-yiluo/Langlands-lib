import Langlands.BushnellKutzko.SubfieldOrderStatement

/-! # Coarsening to an order of relative period one -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

/-- A chain normalized by the units of a subfield has a coarsening that retains
the zeroth lattice and whose relative chain has period one. -/
def SubfieldPeriodOneCoarseningStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type uE) [Field E] [Algebra F E]
    (V : Type uV) [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
    (L : LatticeChain 𝒪[F] F V),
    (∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) →
    ∃ M : LatticeChain 𝒪[F] F V,
      (∀ a : Eˣ, subfieldUnits F E V a ∈ M.stabilizer) ∧
      M.lattice 0 = L.lattice 0 ∧ M.period = subfieldRamificationIndex F E ∧
      L.unitFiltration 0 ≤ M.unitFiltration 0 ∧ M.unitFiltration 1 ≤ L.unitFiltration 1 ∧
      ∃ C : LatticeChain (subfieldIntegers F E) E V,
        C.period = 1 ∧ ∀ i : ℤ, (C.lattice i : Set V) = M.lattice i

end Langlands.BushnellKutzko
