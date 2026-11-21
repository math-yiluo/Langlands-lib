import Langlands.BushnellKutzko.CriticalDerivedSymbols

/-! # The residue map determined by matching scalar symbols -/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko.CriticalDerived

open StratumEquivalence

universe uF uV uE uK

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  {K : Type uK} [Field K] [Algebra F K] [Module K V] [IsScalarTower F K V]
  (hK : ∀ u : Kˣ, subfieldUnits F K V u ∈ 𝓛.stabilizer)

local notation "P" => 𝓛.endFiltration
local notation "ιK" => subfieldEmbedding F K V
local notation "Uₖ" => subfieldUnits F K V
local notation "Oₖ" => subfieldIntegers F K

section Units

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hK in
/-- The shift of a scalar unit is its exact ambient degree. -/
theorem scalar_shifts (u : Kˣ) : Shifts 𝓛 (shift 𝓛 hK (u : K)) (Uₖ u) := by
  rw [shift_of_ne_zero 𝓛 hK u.ne_zero, Units.mk0_val]
  exact Shifts.of_stabilizer ⟨Uₖ u, hK u⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hK in
/-- A scalar matching a nonzero symbol is itself a unit of the exact degree. -/
theorem exists_matching_scalar_unit {d : ℤ} {x : Module.End F V} (hx : x ∉ P (d + 1))
    (hm : ∃ c : K, SymbolEq 𝓛 d x (ιK c)) :
    ∃ u : Kˣ, Shifts 𝓛 d (Uₖ u) ∧ SymbolEq 𝓛 d x (Uₖ u : Module.End F V) := by
  obtain ⟨c, hc⟩ := hm
  have hc' := hc.symm.not_mem_succ hx
  have hcn : c ≠ 0 := by rintro rfl; exact hc' (by simp)
  have hiff := subfieldEmbedding_mem_iff_le 𝓛 (smul_mem_shift_iff 𝓛 hK hcn)
  have h := (hiff d).mp hc.2.1
  have h' : ¬ d + 1 ≤ shift 𝓛 hK c := fun hh => hc' ((hiff _).mpr hh)
  have heq : shift 𝓛 hK c = d := by omega
  refine ⟨Units.mk0 c hcn, ?_, hc⟩
  have hs := scalar_shifts 𝓛 hK (Units.mk0 c hcn)
  rwa [Units.val_mk0, heq] at hs

end Units

section Residue

variable [FiniteDimensional F K]
local instance : IsDiscreteValuationRing Oₖ := subfieldIntegers_isDiscreteValuationRing F K
local notation "kₖ" => ResidueField Oₖ

include hK in
theorem scalar_mem_zero_iff (c : K) : ιK c ∈ P 0 ↔ c ∈ Oₖ := by
  by_cases h : c = 0
  · simp [h]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Oₖ
  exact (subfieldEmbedding_mem_iff_le 𝓛 (smul_mem_shift_iff 𝓛 hK h) 0).trans
    (mem_integers_iff 𝓛 hK hπ h).symm

include hK in
theorem scalar_mem_one_iff (c : Oₖ) : ιK (c : K) ∈ P 1 ↔ residue Oₖ c = 0 := by
  by_cases h : c = 0
  · simp [h]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Oₖ
  have h' : (c : K) ≠ 0 := fun h0 => h (Subtype.ext h0)
  rw [subfieldEmbedding_mem_iff_le 𝓛 (smul_mem_shift_iff 𝓛 hK h') 1,
    ← mem_maximalIdeal_iff 𝓛 hK hπ h, subfieldMaximalIdeal_eq, residue_eq_zero_iff]

include hK in
theorem residue_eq_of_symbolEq {c c' : Oₖ} (h : SymbolEq 𝓛 0 (ιK (c : K)) (ιK (c' : K))) :
    residue Oₖ c = residue Oₖ c' := by
  have hm := h.2.2
  rw [← map_sub] at hm
  have he := (scalar_mem_one_iff 𝓛 hK (c - c')).mp hm
  rwa [map_sub, sub_eq_zero] at he

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  [FiniteDimensional F E] (hE : ∀ u : Eˣ, subfieldUnits F E V u ∈ 𝓛.stabilizer)

local notation "ιE" => subfieldEmbedding F E V
local notation "Oₑ" => subfieldIntegers F E
local instance : IsDiscreteValuationRing Oₑ := subfieldIntegers_isDiscreteValuationRing F E
local notation "kₑ" => ResidueField Oₑ

include hE hK in
/-- Matching scalar symbols induce a map on residue fields, characterized by the residue of
any degree-zero match. This does not require a map between the extension fields. -/
theorem exists_residue_map (hm : ∀ e : E, ιE e ∈ P 0 → ∃ c : K, SymbolEq 𝓛 0 (ιE e) (ιK c)) :
    ∃ ι : kₑ →+* kₖ, ∀ x : Oₑ, ∃ y : Oₖ,
      SymbolEq 𝓛 0 (ιE (x : E)) (ιK (y : K)) ∧ ι (residue Oₑ x) = residue Oₖ y := by
  have hex (x : Oₑ) : ∃ y : Oₖ, SymbolEq 𝓛 0 (ιE (x : E)) (ιK (y : K)) := by
    obtain ⟨c, hc⟩ := hm x ((scalar_mem_zero_iff 𝓛 hE x).mpr x.2)
    exact ⟨⟨c, (scalar_mem_zero_iff 𝓛 hK c).mp hc.2.1⟩, hc⟩
  choose y hy using hex
  let f : Oₑ →+* kₖ := {
    toFun x := residue Oₖ (y x)
    map_zero' := by
      apply (scalar_mem_one_iff 𝓛 hK (y 0)).mp
      simpa using (hy 0).symm.2.2
    map_one' := by
      rw [← (residue Oₖ).map_one]
      exact residue_eq_of_symbolEq 𝓛 hK (by simpa using (hy 1).symm)
    map_add' x x' := by
      rw [← map_add]
      apply residue_eq_of_symbolEq 𝓛 hK
      exact (hy (x + x')).symm.trans (by
        simpa only [Subalgebra.coe_add, map_add] using (hy x).add (hy x'))
    map_mul' x x' := by
      rw [← map_mul]
      apply residue_eq_of_symbolEq 𝓛 hK
      exact (hy (x * x')).symm.trans (by
        simpa only [Subalgebra.coe_mul, map_mul, add_zero] using (hy x).mul (hy x')) }
  let ι : kₑ →+* kₖ := Ideal.Quotient.lift (maximalIdeal Oₑ) f fun x hx => by
    have hx' := (scalar_mem_one_iff 𝓛 hE x).mpr ((residue_eq_zero_iff x).mpr hx)
    exact (scalar_mem_one_iff 𝓛 hK (y x)).mp (by
      simpa only [zero_add, sub_sub_cancel] using sub_mem hx' (hy x).2.2)
  exact ⟨ι, fun x => ⟨y x, hy x, rfl⟩⟩

end Residue

end Langlands.BushnellKutzko.CriticalDerived
