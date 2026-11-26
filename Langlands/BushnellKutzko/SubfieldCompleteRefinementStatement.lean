import Langlands.BushnellKutzko.SubfieldOrderStatement

/-! # Complete refinement of a subfield-normalized lattice chain -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

/-- A chain normalized by the parameter field admits a refinement whose relative
period equals the dimension over the parameter field. -/
def SubfieldCompleteRefinementStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type uE) [Field E] [Algebra F E]
    (V : Type uV) [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
    (L : LatticeChain 𝒪[F] F V),
    (∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) →
    ∃ M : LatticeChain 𝒪[F] F V,
      (∀ a : Eˣ, subfieldUnits F E V a ∈ M.stabilizer) ∧
      M.lattice 0 = L.lattice 0 ∧ (∀ i : ℤ, ∃ j : ℤ, M.lattice j = L.lattice i) ∧
      M.period = subfieldRamificationIndex F E * Module.finrank E V ∧
      M.unitFiltration 0 ≤ L.unitFiltration 0 ∧ L.unitFiltration 1 ≤ M.unitFiltration 1 ∧
      ∃ C : LatticeChain (subfieldIntegers F E) E V,
        C.period = Module.finrank E V ∧ ∀ i : ℤ, (C.lattice i : Set V) = M.lattice i

end Langlands.BushnellKutzko
