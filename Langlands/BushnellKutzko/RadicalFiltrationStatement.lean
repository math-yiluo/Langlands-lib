import Langlands.BushnellKutzko.LatticeChain

/-! # The radical filtration of a hereditary order (Bushnell–Kutzko 1993, §1.1, pp. 21–22) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u v

/-- **BK93 §1.1, printed pp. 21–22.** Let `F` be a nonarchimedean local field, `V` an `F`-vector
space and `𝓛 = (L_i)` an `𝔬_F`-lattice chain in `V`, with order `𝔄 = 𝔄(𝓛)` and lattices
`𝔓^n = End^n_{𝔬_F}(𝓛)` in `A = End_F(V)`. Then
1. `𝔓^m 𝔓^n = 𝔓^{m+n}` for all `m, n ∈ ℤ` (product of `𝔬_F`-submodules of `A`);
2. `𝔓^n L_i = L_{i+n}` for all `n, i ∈ ℤ`, where `𝔓^n L_i` is the `𝔬_F`-span of the vectors
   `x v` with `x ∈ 𝔓^n`, `v ∈ L_i`;
3. `𝔭_F 𝔄 = 𝔓^{e(𝓛)}`;
4. `𝔓^1` is the Jacobson radical of `𝔄`;
5. for `x ≠ 0` in `A`, the set `{n ∈ ℤ : x ∈ 𝔓^n}` is nonempty and bounded above, so that
   `v_𝔄(x) = max {n : x ∈ 𝔓^n}` of (1.1.3) exists. -/
def RadicalFiltrationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type v) [AddCommGroup V] [Module F V] (𝓛 : LatticeChain 𝒪[F] F V),
    (∀ m n : ℤ, 𝓛.endFiltration m * 𝓛.endFiltration n = 𝓛.endFiltration (m + n)) ∧
    (∀ n i : ℤ,
      Submodule.span 𝒪[F]
          (Set.image2 (fun (x : Module.End F V) (w : V) => x w)
            (𝓛.endFiltration n : Set (Module.End F V)) (𝓛.lattice i : Set V)) =
        𝓛.lattice (i + n)) ∧
    𝓂[F] • Subalgebra.toSubmodule 𝓛.order = 𝓛.endFiltration 𝓛.period ∧
    (∀ x : 𝓛.order, x ∈ Ring.jacobson 𝓛.order ↔ (x : Module.End F V) ∈ 𝓛.endFiltration 1) ∧
    ∀ x : Module.End F V, x ≠ 0 →
      {n : ℤ | x ∈ 𝓛.endFiltration n}.Nonempty ∧ BddAbove {n : ℤ | x ∈ 𝓛.endFiltration n}

end Langlands.BushnellKutzko
