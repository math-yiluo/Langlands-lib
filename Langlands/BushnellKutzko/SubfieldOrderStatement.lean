import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.SubfieldIntegers

/-! # The hereditary order `𝔅 = 𝔄 ∩ B` (Bushnell–Kutzko 1993, (1.2.2)–(1.2.4), p. 25) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u v w

/-- **BK93 (1.2.2)–(1.2.4), printed p. 25.** Let `F`, `V`, `𝓛`, `𝔄 = 𝔄(𝓛)` and `E` be as in
`SubfieldNormalizerStatement`, and suppose `E^× ⊆ 𝔎(𝔄)`. Let `B = End_E(V)`, the centralizer of
`E` in `A = End_F(V)`, embedded in `A` by restriction of scalars. Then there is an
`𝔬_E`-lattice chain `𝓛'` in the `E`-vector space `V` with the same lattices as `𝓛` such that
1. `𝔅 = 𝔄 ∩ B` is the hereditary `𝔬_E`-order `𝔄(𝓛')`;
2. `𝔓^n ∩ B = End^n_{𝔬_E}(𝓛') = 𝔔^n` for every `n ∈ ℤ`;
3. `𝔔^m 𝔔^n = 𝔔^{m+n}` for all `m, n ∈ ℤ`, and `𝔔 = 𝔔^1` is the Jacobson radical of `𝔅`;
4. `e(𝔄 | 𝔬_F) = e(E|F) · e(𝔅 | 𝔬_E)`, i.e. `e(𝓛) = e(E|F) · e(𝓛')`. -/
def SubfieldOrderStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type v) [AddCommGroup V] [Module F V]
    (E : Type w) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (𝓛 : LatticeChain 𝒪[F] F V),
    (∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) →
    ∃ 𝓛' : LatticeChain (subfieldIntegers F E) E V,
      (∀ i : ℤ, (𝓛'.lattice i : Set V) = 𝓛.lattice i) ∧
      (∀ y : Module.End E V, y ∈ 𝓛'.order ↔ y.restrictScalars F ∈ 𝓛.order) ∧
      (∀ (n : ℤ) (y : Module.End E V),
        y ∈ 𝓛'.endFiltration n ↔ y.restrictScalars F ∈ 𝓛.endFiltration n) ∧
      (∀ m n : ℤ, 𝓛'.endFiltration m * 𝓛'.endFiltration n = 𝓛'.endFiltration (m + n)) ∧
      (∀ y : 𝓛'.order, y ∈ Ring.jacobson 𝓛'.order ↔ (y : Module.End E V) ∈ 𝓛'.endFiltration 1) ∧
      𝓛.period = subfieldRamificationIndex F E * 𝓛'.period

end Langlands.BushnellKutzko
