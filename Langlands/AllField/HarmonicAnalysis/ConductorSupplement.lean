import Langlands.HarmonicAnalysis.Conductor
import Langlands.AllField.HarmonicAnalysis.Conductor
/-! Conductors from the actual discrete valuation of a finite p-adic field. -/

noncomputable section

open scoped WithZero
open Topology

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe u
variable {F : Type u} [Field F] (T : LocalFieldData F)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F _ T.topology
local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F _ T.topology

open Langlands.HarmonicAnalysis

/-- The unit filtration, including `U⁰ = Oˣ`. For positive `n` the second
condition is the usual congruence to one modulo the `n`th maximal-ideal power. -/
def principalUnits (n : ℕ) : Subgroup Fˣ where
  carrier := {u | T.discreteValuation (u : F) = 1 ∧
    T.discreteValuation ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    constructor
    · simpa using congrArg₂ (· * ·) hu.1 hv.1
    · change T.discreteValuation ((u : F) * v - 1) ≤ _
      rw [show (u : F) * v - 1 =
        u * ((v : F) - 1) + ((u : F) - 1) by ring]
      apply T.discreteValuation.map_add_le _ hu.2
      simpa [map_mul, hu.1] using hv.2
  inv_mem' := by
    intro u hu
    constructor
    · simpa using congrArg Inv.inv hu.1
    · simp only [Units.val_inv_eq_inv_val]
      rw [show (u : F)⁻¹ - 1 =
        -((u : F) - 1) * (u : F)⁻¹ by
          field_simp
          ring]
      simpa only [map_mul, Valuation.map_neg, map_inv₀, hu.1, inv_one, mul_one] using hu.2

@[simp]
theorem mem_principalUnits (n : ℕ) (u : Fˣ) :
    u ∈ T.principalUnits n ↔ T.discreteValuation (u : F) = 1 ∧
      T.discreteValuation ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := Iff.rfl

/-- The congruence condition is measured against the actual fractional ideal
`π^n O`; no arbitrary filtration is supplied as an input. -/
theorem mem_principalUnits_iff_div_mem_integers (n : ℕ) (u : Fˣ) :
    u ∈ T.principalUnits n ↔ T.discreteValuation (u : F) = 1 ∧
      ((u : F) - 1) / T.uniformizer ^ (n : ℤ) ∈ T.Integers := by
  change (T.discreteValuation (u : F) = 1 ∧
    (u : F) - 1 ∈ T.additiveLattice (-(n : ℤ))) ↔ _
  rw [T.mem_additiveLattice_iff_div_mem_integers]
  simp only [neg_neg]

theorem principalUnits_antitone : Antitone T.principalUnits := by
  intro m n h u hu
  exact ⟨hu.1, hu.2.trans (WithZero.exp_le_exp.mpr (by omega))⟩

/-- The actual principal-unit groups are cofinal among neighborhoods of one. -/
theorem exists_principalUnits_subset {s : Set Fˣ}
    (hs : letI := T.topology; s ∈ 𝓝 (1 : Fˣ)) :
    ∃ n : ℕ, (T.principalUnits n : Set Fˣ) ⊆ s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hs
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp hs
  have ht' : (fun x : F => x + 1) ⁻¹' t ∈ 𝓝 (0 : F) := by
    exact (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using ht)
  obtain ⟨k, hk⟩ := T.exists_additiveLattice_subset ht'
  refine ⟨(-k).toNat, fun u hu => hts ?_⟩
  have hu' : ((u : F) - 1) ∈ T.additiveLattice k :=
    hu.2.trans (WithZero.exp_le_exp.mpr (by omega))
  simpa using hk hu'

/-- Triviality of a quasicharacter on the actual `n`th unit subgroup. -/
def MultiplicativeTrivialAt (χ : MultiplicativeCharacter) (n : ℕ) : Prop :=
  ∀ u ∈ T.principalUnits n, χ u = 1

/-- Continuous complex quasicharacters are trivial at some principal-unit level.
The no-small-subgroups input is the already proved complex power estimate. -/
theorem exists_multiplicativeTrivialAt (χ : MultiplicativeCharacter) :
    ∃ n : ℕ, T.MultiplicativeTrivialAt χ n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let s : Set Fˣ := {u | ‖(χ u : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hs : s ∈ 𝓝 (1 : Fˣ) := by
    apply (isOpen_lt ((Units.continuous_val.comp χ.continuous).sub
      continuous_const).norm continuous_const).mem_nhds
    simp
  obtain ⟨n, hn⟩ := T.exists_principalUnits_subset hs
  refine ⟨n, fun u hu => ?_⟩
  apply Units.ext
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro k
  simpa [s] using hn ((T.principalUnits n).pow_mem hu k)

/-- Tate's conductor exponent `a(χ)`: the least unit-filtration level on which
the quasicharacter is trivial, with zero precisely in the unramified case. -/
def multiplicativeConductor (χ : MultiplicativeCharacter) : ℕ := by
  classical
  exact Nat.find (T.exists_multiplicativeTrivialAt χ)

theorem multiplicativeConductor_spec (χ : MultiplicativeCharacter) :
    T.MultiplicativeTrivialAt χ (T.multiplicativeConductor χ) := by
  classical
  exact Nat.find_spec (T.exists_multiplicativeTrivialAt χ)

theorem multiplicativeTrivialAt_iff_conductor_le (χ : MultiplicativeCharacter)
    (n : ℕ) : T.MultiplicativeTrivialAt χ n ↔ T.multiplicativeConductor χ ≤ n := by
  classical
  constructor
  · exact Nat.find_min' (T.exists_multiplicativeTrivialAt χ)
  · intro hn u hu
    exact T.multiplicativeConductor_spec χ u (T.principalUnits_antitone hn hu)

/-- Every strictly lower unit level contains a nontrivial character value. -/
theorem exists_nontrivial_below_multiplicativeConductor
    (χ : MultiplicativeCharacter) (n : ℕ) (hn : n < T.multiplicativeConductor χ) :
    ∃ u ∈ T.principalUnits n, χ u ≠ 1 := by
  by_contra h
  push Not at h
  exact (not_le.mpr hn) ((T.multiplicativeTrivialAt_iff_conductor_le χ n).mp h)

end Langlands.LocalFieldData
