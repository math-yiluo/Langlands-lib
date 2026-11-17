import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.SubfieldIntegers

/-! # Subfields normalizing a hereditary order (Bushnell–Kutzko 1993, (1.2.1), p. 24) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u v w

/-- **BK93 (1.2.1), printed p. 24.** Let `F` be a nonarchimedean local field, `V` an `F`-vector
space, `𝓛 = (L_i)` an `𝔬_F`-lattice chain in `V` with order `𝔄 = 𝔄(𝓛)`, and `E` a field
extension of `F` acting `F`-linearly on `V` (a subfield of `A = End_F(V)` containing `F`). The
following are equivalent:
1. `E^× ⊆ 𝔎(𝔄)`;
2. each `L_i` is an `𝔬_E`-module and there is an integer `e'` with `𝔭_E L_i = L_{i+e'}` for all
   `i`, where `𝔭_E L_i` is the `𝔬_F`-span of the vectors `a v` with `a ∈ 𝔭_E`, `v ∈ L_i`. -/
def SubfieldNormalizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type v) [AddCommGroup V] [Module F V]
    (E : Type w) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (𝓛 : LatticeChain 𝒪[F] F V),
    (∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) ↔
      ((∀ i : ℤ, ∀ a ∈ subfieldIntegers F E, ∀ w ∈ 𝓛.lattice i, a • w ∈ 𝓛.lattice i) ∧
        ∃ e' : ℤ, ∀ i : ℤ,
          Submodule.span 𝒪[F]
              (Set.image2 (fun (a : subfieldIntegers F E) (w : V) => (a : E) • w)
                (subfieldMaximalIdeal F E : Set (subfieldIntegers F E)) (𝓛.lattice i : Set V)) =
            𝓛.lattice (i + e'))

end Langlands.BushnellKutzko
