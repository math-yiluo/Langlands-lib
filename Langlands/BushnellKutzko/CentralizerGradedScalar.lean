import Langlands.BushnellKutzko.CriticalDerivedScalars
import Langlands.BushnellKutzko.StratumEquivalenceResidue

/-! # Elements commuting with the centralizer filtration up to one step

Let a field `E` act on `V` with `E^×` normalizing the `𝔬_F`-lattice chain `𝓛`, and write
`𝔓^j = 𝓛.endFiltration j`. An endomorphism `b ∈ 𝔄` whose commutator with every
`E`-linear element of `𝔓^j` lies in `𝔓^{j+1}`, for all `j ∈ ℤ`, is congruent modulo `𝔓` to an
element of `𝔬_E`.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

namespace StratumEquivalence

universe uF uV uE

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

local notation "L" => 𝓛.lattice
local notation "P" => 𝓛.endFiltration

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]
  [FiniteDimensional F E]

include hE in
/-- An element of `𝔄` commuting modulo one more step with every `E`-linear element of every
`𝔓^j` is congruent modulo `𝔓` to an element of `𝔬_E`. -/
theorem exists_integer_sub_mem_of_commutator {b : Module.End F V} (hb : b ∈ P 0)
    (hcomm : ∀ (j : ℤ) (y : Module.End F V), y ∈ P j → y ∈ fieldCommutant E →
      b * y - y * b ∈ P (j + 1)) :
    ∃ a ∈ subfieldIntegers F E, b - subfieldEmbedding F E V a ∈ P 1 := by
  obtain ⟨n, w, k, c, hw, hu⟩ := exists_basis_depth_zero 𝓛 hE
  have hc : c ≠ 0 := by
    rintro rfl
    exact hu.ne_zero 𝓛 (zero_smul E _)
  set u := c • w k with hudef
  set μ : E := w.coord k (b u) * c⁻¹ with hμdef
  have key : ∀ (j : ℤ), ∀ y ∈ L j, b y - μ • y ∈ L (j + 1) := by
    intro j y hy
    have hR := hcomm j (rankOne F w k c y) (CriticalDerived.rankOne_mem_endFiltration 𝓛 hE hw hu hy)
      (rankOne_mem_fieldCommutant k c y)
    have h := hR 0 u hu.1
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      rankOne_apply_basis k hc, rankOne_apply, smul_smul, zero_add] at h
    exact h
  refine ⟨μ, ?_, fun i v hv => ?_⟩
  · by_cases hμ : μ = 0
    · rw [hμ]
      exact zero_mem _
    have := subfieldIntegers_isDiscreteValuationRing F E
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
    rw [mem_integers_iff 𝓛 hE hϖ hμ]
    have hmem : μ • u ∈ L 0 := by
      have hbu : b u ∈ L 0 := by simpa using hb 0 u hu.1
      have h := coord_smul_mem 𝓛 hw hbu k
      rwa [hudef, hμdef, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    have hle := (hu.smul 𝓛 hE hμ).le 𝓛 hmem
    omega
  · have h := key i v hv
    rwa [LinearMap.sub_apply, subfieldEmbedding_apply]

end StratumEquivalence

end Langlands.BushnellKutzko
