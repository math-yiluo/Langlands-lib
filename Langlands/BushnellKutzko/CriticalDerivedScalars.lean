import Langlands.BushnellKutzko.CriticalDerivedCentralizer
import Langlands.BushnellKutzko.StratumEquivalenceResidueDegree

/-! # Recognizing scalar symbols in the critical derived comparison -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.CriticalDerived

open StratumEquivalence

universe uF uV uE uK

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (𝓛 : LatticeChain 𝒪[F] F V)

local notation "L" => 𝓛.lattice
local notation "P" => 𝓛.endFiltration

section Scalar

variable {K : Type uK} [Field K] [Algebra F K] [Module K V] [IsScalarTower F K V]
  (hK : ∀ u : Kˣ, subfieldUnits F K V u ∈ 𝓛.stabilizer)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
include hK in
/-- The rank-one map carrying a splitting basis vector of depth zero to `y ∈ L_i`
has depth at least `i`. -/
theorem rankOne_mem_endFiltration {n : ℕ} {w : Module.Basis (Fin n) K V}
    (hw : RelativeSplits (E := K) 𝓛 w) {k : Fin n} {c : K} (hu : ExactDepth 𝓛 (c • w k) 0)
    {i : ℤ} {y : V} (hy : y ∈ L i) : rankOne F w k c y ∈ P i := by
  intro j v hv
  have hc : c ≠ 0 := fun hc => hu.ne_zero 𝓛 (by rw [hc, zero_smul])
  rw [rankOne_apply, smul_smul]
  by_cases hs : w.coord k v * c⁻¹ = 0
  · rw [hs, zero_smul]
    exact zero_mem _
  have hsu : (w.coord k v * c⁻¹) • (c • w k) ∈ L j := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    exact coord_smul_mem 𝓛 hw hv k
  have hle := (hu.smul 𝓛 hK hs).le 𝓛 hsu
  exact smul_mem_of_shift_le 𝓛 hK hs (by omega) hy

include hK in
/-- An ambient homogeneous symbol commuting with the whole graded centralizer of `K`
is the symbol of a scalar of `K`. No `K`-linearity of the ambient representative is needed. -/
theorem exists_scalar_of_graded_commutation {j : ℤ} {z : Module.End F V} (hz : z ∈ P j)
    (hcomm : ∀ (i : ℤ) (m : Module.End F V), m ∈ P i → m ∈ fieldCommutant K →
      z * m - m * z ∈ P (j + i + 1)) :
    ∃ c : K, subfieldEmbedding F K V c ∈ P j ∧ z - subfieldEmbedding F K V c ∈ P (j + 1) := by
  obtain ⟨n, w, k, b, hw, hu⟩ := exists_basis_depth_zero 𝓛 hK
  have hb : b ≠ 0 := fun hb => hu.ne_zero 𝓛 (by rw [hb, zero_smul])
  let u := b • w k
  let c := w.coord k (z u) * b⁻¹
  have hcu : c • u = w.coord k (z u) • w k := by
    simp only [c, u, smul_smul, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hzu : z u ∈ L j := by simpa only [zero_add] using hz 0 u hu.1
  have hcp : subfieldEmbedding F K V c ∈ P j := by
    by_cases hc : c = 0
    · rw [hc, map_zero]
      exact zero_mem _
    apply (subfieldEmbedding_mem_iff_le 𝓛 (smul_mem_shift_iff 𝓛 hK hc) j).2
    have hcdepth := hu.smul 𝓛 hK hc
    rw [zero_add] at hcdepth
    exact hcdepth.le 𝓛 (hcu ▸ coord_smul_mem 𝓛 hw hzu k)
  have h0 : z u - c • u ∈ L (j + 1) := by
    let p := rankOne F w k b u
    have hp := rankOne_mem_endFiltration 𝓛 hK hw hu hu.1
    have h := hcomm 0 p hp (rankOne_mem_fieldCommutant k b u) 0 u hu.1
    have hpu : p u = u := rankOne_apply_basis k hb u
    have hpzu : p (z u) = c • u := by rw [rankOne_apply, smul_smul]
    simpa only [zero_add, add_zero, LinearMap.sub_apply, Module.End.mul_apply, hpu, hpzu] using h
  refine ⟨c, hcp, fun i y hy => ?_⟩
  let m := rankOne F w k b y
  have hm := rankOne_mem_endFiltration 𝓛 hK hw hu hy
  have hmK : m ∈ fieldCommutant K := rankOne_mem_fieldCommutant k b y
  have hmu : m u = y := rankOne_apply_basis k hb y
  have h1 := hcomm i m hm hmK 0 u hu.1
  have h2 := hm (j + 1) (z u - c • u) h0
  change z y - c • y ∈ L (i + (j + 1))
  have heq : z y - c • y = (z * m - m * z) u + m (z u - c • u) := by
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, map_sub, hmK c u, hmu]
    abel
  rw [heq, show i + (j + 1) = (j + 1) + i by omega]
  refine add_mem ?_ h2
  rwa [show j + 1 + i = 0 + (j + i + 1) by omega]

end Scalar

section Transfer

variable {β γ a : Module.End F V} {d : ℤ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
/-- A symbol centralizing the original centralizer symbols in the required degrees
also centralizes the perturbed centralizer symbols. -/
theorem graded_commutation_of_approx
    (hf : ∀ (i : ℤ) (x : Module.End F V), x ∈ P i → Commute x β →
      ∃ y ∈ P i, Commute y γ ∧ x - y ∈ P (i + 1) ∧ a * y - y * a ∈ P (d + i + 1))
    {j : ℤ} {z : Module.End F V} (hz : z ∈ P j)
    (hzc : ∀ (i : ℤ) (y : Module.End F V), Commute y γ →
      a * y - y * a ∈ P (d + i + 1) → z * y - y * z ∈ P (j + i + 1))
    (i : ℤ) {x : Module.End F V} (hx : x ∈ P i) (hxc : Commute x β) :
    z * x - x * z ∈ P (j + i + 1) := by
  obtain ⟨y, -, hyγ, hxy, hya⟩ := hf i x hx hxc
  have h := commutator_mem_endFiltration 𝓛 hz hxy
  rw [← add_assoc] at h
  have heq : z * x - x * z = (z * y - y * z) + (z * (x - y) - (x - y) * z) := by noncomm_ring
  rw [heq]
  exact add_mem (hzc i y hyγ hya) h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V] in
/-- At a critical index of the perturbed element the derived symbol cannot vanish. -/
theorem not_mem_succ_of_critical
    (hb : β - γ ∈ P d) (hd : d ∈ criticalIndexSet 𝓛 β)
    (hγ : ∀ x : Module.End F V, γ * x - x * γ ∈ P d → ∃ y, Commute y γ ∧ x - y ∈ P 1)
    (hbwd : ∀ x ∈ P (0 : ℤ), Commute x γ → a * x - x * a ∈ P (d + 1) →
      ∃ y ∈ P (0 : ℤ), Commute y β ∧ x - y ∈ P 1) : a ∉ P (d + 1) := by
  intro ha
  apply (mem_criticalIndexSet_iff_commute 𝓛 β d).mp hd
  intro x hx
  have hb' : β - γ ∈ P (-(-d)) := by simpa only [neg_neg] using hb
  have hx' := (mem_adjointLattice_iff_of_sub_mem 𝓛 hb' (r := -d) (by omega) x).1 hx
  obtain ⟨y, hyγ, hxy⟩ := hγ x hx'.2
  have hy := sub_mem (show x ∈ P 0 from hx.1)
    (𝓛.endFiltration_antitone (show (0 : ℤ) ≤ 1 by omega) hxy)
  rw [sub_sub_cancel] at hy
  have hya : a * y - y * a ∈ P (d + 1) := by
    simpa only [add_zero] using commutator_mem_endFiltration 𝓛 ha hy
  obtain ⟨z, -, hzβ, hyz⟩ := hbwd y hy hyγ hya
  exact ⟨z, hzβ, by rw [show x - z = (x - y) + (y - z) by abel]; exact add_mem hxy hyz⟩

end Transfer

end Langlands.BushnellKutzko.CriticalDerived
