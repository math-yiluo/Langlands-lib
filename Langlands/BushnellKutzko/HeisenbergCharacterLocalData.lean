import Langlands.BushnellKutzko.SimpleCharacters
import Langlands.BushnellKutzko.AdjointLatticeBounds
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.RadicalFiltrationProof
import Langlands.BushnellKutzko.UnitFiltrationQuotient
import Mathlib.GroupTheory.Index

/-! # Deep unit subgroups and simple characters -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type v} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V)

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "P" => L.endFiltration
local notation "U" => L.unitFiltration

/-- Every positive-depth step has finite relative index in `U^1`. -/
theorem LatticeChain.unitFiltration_finiteIndex_in_one (k : ℕ) :
    ((U (k + 1)).subgroupOf (U 1)).FiniteIndex := by
  have step (i : ℕ) (hi : 1 ≤ i) : ((U (i + 1)).subgroupOf (U i)).FiniteIndex := by
    let T := (P (i + 1 : ℕ)).comap (P (i : ℤ)).subtype
    let Q := (P (i : ℤ)) ⧸ T
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have hP : 𝓂[F] • P (i : ℤ) ≤ P (i + 1 : ℕ) := by
      rw [hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul,
        ← L.endFiltration_add_period_eq_smul hϖ]
      apply L.endFiltration_antitone
      have := L.period_pos
      exact_mod_cast (show i + 1 ≤ i + L.period by omega)
    have hann : Module.IsTorsionBySet 𝒪[F] Q (𝓂[F] : Set 𝒪[F]) :=
      (Module.isTorsionBySet_quotient_iff _ _).mpr fun x a ha =>
        hP (Submodule.smul_mem_smul ha x.2)
    let := hann.module
    have : IsScalarTower 𝒪[F] (𝒪[F] ⧸ 𝓂[F]) Q := hann.isScalarTower
    have : Module.Finite 𝒪[F] (P (i : ℤ)) := Module.Finite.iff_fg.mpr (L.fg_endFiltration i)
    have : Module.Finite (𝒪[F] ⧸ 𝓂[F]) Q :=
      Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
    have : Finite Q := Module.finite_of_finite (𝒪[F] ⧸ 𝓂[F])
    let f := L.unitFiltrationToQuotient (i := i) (j := i + 1) (by omega)
    have hker : f.ker = (U (i + 1)).subgroupOf (U i) :=
      Subgroup.ext (L.mem_ker_unitFiltrationToQuotient (by omega))
    rw [← hker]
    infer_instance
  induction k with
  | zero =>
    rw [Nat.zero_add, Subgroup.subgroupOf_self]
    infer_instance
  | succ k ih =>
    have hs := (step (k + 1) (by omega)).index_ne_zero
    have he := Subgroup.relIndex_mul_relIndex (U (k + 2)) (U (k + 1)) (U 1)
      (L.unitFiltration_antitone (by omega)) (L.unitFiltration_antitone (by omega))
    refine ⟨?_⟩
    change (U (k + 2)).relIndex (U 1) ≠ 0
    rw [← he]
    exact mul_ne_zero hs ih.index_ne_zero

variable (n : ℤ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizerLattice_le_simpleHLattice (β : A) (tail : List A) :
    centralizerLattice L β 0 ≤ simpleHLattice L n β tail := by
  cases tail <;> exact le_sup_left

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem unitFiltration_le_simpleHGroup (β : A) (tail : List A) (m : ℕ) :
    ∃ k : ℕ, m ≤ k ∧ U k ≤ simpleHGroup L n β tail m := by
  have hl (β : A) (tail : List A) : ∃ k : ℕ, P (k : ℤ) ≤ simpleHLattice L n β tail := by
    induction tail generalizing β with
    | nil =>
      refine ⟨(simpleHCutoff n).toNat, ?_⟩
      exact (L.endFiltration_antitone (Int.self_le_toNat _)).trans le_sup_right
    | cons γ tail ih =>
      obtain ⟨k, hk⟩ := ih γ
      let j := max k (simpleHCutoff (finiteCriticalDepth L n β)).toNat
      refine ⟨j, le_sup_of_le_right (le_inf ?_ ?_)⟩
      · exact (L.endFiltration_antitone (by exact_mod_cast le_max_left k _)).trans hk
      · exact L.endFiltration_antitone ((Int.self_le_toNat _).trans (by
          exact_mod_cast le_max_right k (simpleHCutoff (finiteCriticalDepth L n β)).toNat))
  obtain ⟨k, hk⟩ := hl β tail
  have hone : (1 : A) ∈ simpleHLattice L n β tail :=
    centralizerLattice_le_simpleHLattice L n β tail
      ⟨L.order.one_mem, by change β * 1 - 1 * β = 0; simp⟩
  refine ⟨max m k, le_max_left _ _, fun g hg => Subgroup.subset_closure ⟨?_, ?_⟩⟩
  · exact L.unitFiltration_antitone (le_max_left _ _) hg
  · have h := add_mem (hk (L.unitFiltration_antitone (le_max_right m k) hg).2.2) hone
    simpa using h

variable {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)

include hψ in
private theorem elementCharacter_eq_one_on_deep_units (β : A) :
    ∃ k : ℕ, ∀ g ∈ U k, elementCharacter (traceCharacter ψF) β g = 1 := by
  have := L.finiteDimensional
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, ha⟩ := L.exists_uniformizer_pow_mem_endFiltration hϖ β 1
  refine ⟨a * L.period, fun g hg => ?_⟩
  have hb : β ∈ P (1 - ((a * L.period : ℕ) : ℤ)) := by
    apply (L.uniformizer_pow_end_mem_iff hϖ a _ β).mp
    simpa only [Nat.cast_mul, sub_add_cancel] using ha
  have htrace := (L.mem_endFiltration_iff_trace_mul _ β).mp hb _ hg.2.2
  obtain ⟨x, hx, heq⟩ := htrace
  rw [elementCharacter_apply, traceCharacter_apply, ← heq]
  exact hψ.1 x hx

include hψ in
/-- A simple character is defined on a sufficiently deep unit subgroup and is trivial there. -/
theorem simpleCharacter_trivial_on_deep_units (β : A) (tail : List A) (m : ℕ)
    {θ : simpleHGroup L n β tail (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n β tail m) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ g ∈ U k,
      ∃ hg : g ∈ simpleHGroup L n β tail (m + 1), θ ⟨g, hg⟩ = 1 := by
  classical
  induction tail generalizing β m with
  | nil =>
    obtain ⟨i, hi, hH⟩ := unitFiltration_le_simpleHGroup L n β [] (m + 1)
    obtain ⟨j, hj⟩ := elementCharacter_eq_one_on_deep_units L hψ β
    let k := max (max i j) (simpleHCutoff n).toNat
    have hik : i ≤ k := (le_max_left i j).trans (le_max_left _ _)
    have hjk : j ≤ k := (le_max_right i j).trans (le_max_left _ _)
    have hc : (simpleHCutoff n).toNat ≤ k := le_max_right _ _
    refine ⟨k, by omega, fun g hg => ⟨hH (L.unitFiltration_antitone hik hg), ?_⟩⟩
    change (∀ g : simpleHGroup L n β [] (m + 1), (g : G) ∈ U (simpleHCutoff n).toNat →
      (θ g : ℂ) = elementCharacter (traceCharacter ψF) β g) ∧ _ at hθ
    apply Units.ext
    exact (hθ.1 _ (L.unitFiltration_antitone hc hg)).trans
      (hj g (L.unitFiltration_antitone hjk hg))
  | cons γ tail ih =>
    unfold simpleCharacters at hθ
    dsimp only at hθ
    by_cases hlt : (m : ℤ) < finiteCriticalDepth L n β
    · rw [ite_eq_left hlt] at hθ
      obtain ⟨-, -, θ₀, hθ₀, hagree⟩ := hθ
      let l := max m (finiteCriticalDepth L n β / 2).toNat
      obtain ⟨i, hi, hθi⟩ := ih γ l hθ₀
      obtain ⟨j, hj⟩ := elementCharacter_eq_one_on_deep_units L hψ (β - γ)
      obtain ⟨d, -, hH⟩ := unitFiltration_le_simpleHGroup L n β (γ :: tail) (l + 1)
      let k := max (max i j) d
      have hik : i ≤ k := (le_max_left i j).trans (le_max_left _ _)
      have hjk : j ≤ k := (le_max_right i j).trans (le_max_left _ _)
      refine ⟨k, hi.trans hik, fun g hg => ?_⟩
      obtain ⟨h₁, h₂, hv⟩ := hagree ⟨g, hH (L.unitFiltration_antitone (le_max_right _ _) hg)⟩
      obtain ⟨h₂', hv₂⟩ := hθi g (L.unitFiltration_antitone hik hg)
      refine ⟨h₁, Units.ext ?_⟩
      rw [hv, show θ₀ ⟨g, h₂⟩ = 1 from hv₂, hj g (L.unitFiltration_antitone hjk hg)]
      simp
    · rw [ite_eq_right hlt] at hθ
      obtain ⟨θ₀, hθ₀, hH, hagree⟩ := hθ
      obtain ⟨i, hi, hθi⟩ := ih γ m hθ₀
      refine ⟨i, hi, fun g hg => ?_⟩
      obtain ⟨h₂, hv₂⟩ := hθi g hg
      obtain ⟨h₁, h₂', hv⟩ := hagree ⟨g, hH ▸ h₂⟩
      refine ⟨h₁, Units.ext ?_⟩
      rw [hv, show θ₀ ⟨g, h₂'⟩ = 1 from hv₂]
      simp

end Langlands.BushnellKutzko
