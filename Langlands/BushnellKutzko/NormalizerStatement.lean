import Langlands.BushnellKutzko.UnitFiltration

/-! # The normalizer `𝔎(𝔄)` of a hereditary order (Bushnell–Kutzko 1993, §1.1, pp. 21–22) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u v

/-- **BK93 §1.1, printed pp. 21–22.** Let `F` be a nonarchimedean local field, `V` an
`F`-vector space, `𝓛 = (L_i)` an `𝔬_F`-lattice chain in `V`, `𝔄 = 𝔄(𝓛)`, `𝔓^n = End^n(𝓛)`
and `G = Aut_F(V)`. Then
1. for every `n ≥ 0`, `U^n(𝔄) ⊆ 𝔎(𝔄)` and `U^n(𝔄)` is a normal subgroup of `𝔎(𝔄)`;
2. `𝔎(𝔄)` is the `G`-normalizer of `𝔄`: `g ∈ 𝔎(𝔄)` if and only if `g 𝔄 g⁻¹ = 𝔄`;
3. for every `n ≥ 0`, `𝔎(𝔄)` is the `G`-normalizer of `U^n(𝔄)`;
4. for `g ∈ 𝔎(𝔄)`, `v_𝔄(g)` (the valuation (1.1.3) of `g` as an element of `A`) equals the
   integer `n` with `g L_i = L_{i+n}`, and `g 𝔄 = 𝔄 g = 𝔓^n`. -/
def NormalizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type v) [AddCommGroup V] [Module F V] (𝓛 : LatticeChain 𝒪[F] F V),
    (∀ n : ℕ, 𝓛.unitFiltration n ≤ 𝓛.stabilizer ∧
      ((𝓛.unitFiltration n).subgroupOf 𝓛.stabilizer).Normal) ∧
    (∀ g : (Module.End F V)ˣ, g ∈ 𝓛.stabilizer ↔
      (fun a : Module.End F V => (g : Module.End F V) * a * ((g⁻¹ : (Module.End F V)ˣ) :
        Module.End F V)) '' (𝓛.order : Set (Module.End F V)) = 𝓛.order) ∧
    (∀ n : ℕ, Subgroup.normalizer (𝓛.unitFiltration n : Set (Module.End F V)ˣ) =
      𝓛.stabilizer) ∧
    ∀ g : 𝓛.stabilizer,
      𝓛.valuation ((g : (Module.End F V)ˣ) : Module.End F V) = 𝓛.stabilizerValuation g ∧
      (fun a : Module.End F V => ((g : (Module.End F V)ˣ) : Module.End F V) * a) ''
          (𝓛.order : Set (Module.End F V)) =
        (𝓛.endFiltration (𝓛.stabilizerValuation g) : Set (Module.End F V)) ∧
      (fun a : Module.End F V => a * ((g : (Module.End F V)ˣ) : Module.End F V)) ''
          (𝓛.order : Set (Module.End F V)) =
        (𝓛.endFiltration (𝓛.stabilizerValuation g) : Set (Module.End F V))

end Langlands.BushnellKutzko
