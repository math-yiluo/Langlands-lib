import Langlands.Representation.Conductor.Definitions
import Mathlib.RingTheory.Filtration

/-!
# Rank-one newvector construction from smoothness

In rank one the congruence subgroups form a neighborhood basis at one.
Thus every nonzero smooth representation has a finite nonzero fixed level.
This argument does not extend to the higher-rank last-row subgroups.
-/

noncomputable section

namespace Langlands.Conductor

universe uR uF uK uV

open Matrix Topology

/-- The intersection of the rank-one integral congruence groups is trivial. -/
theorem rankOne_integral_iInter {R : Type uR} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    (⋂ a : ℕ, (integralCongruence 0 (IsLocalRing.maximalIdeal R ^ a) :
      Set (GeneralLinearGroup (Fin 1) R))) = {1} := by
  ext g
  constructor
  · intro hg
    have hx : g 0 0 - 1 ∈ (⨅ a : ℕ, IsLocalRing.maximalIdeal R ^ a) := by
      simp only [Submodule.mem_iInf]
      intro a
      exact (mem_integralCongruence_rankOne _ g).1 (Set.mem_iInter.mp hg a)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hx
    have he : g 0 0 = 1 := sub_eq_zero.mp hx
    apply Set.mem_singleton_iff.mpr
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i
    fin_cases j
    simpa using he
  · rintro rfl
    exact Set.mem_iInter.mpr fun a => (integralCongruence 0 _).one_mem

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Rank-one level subgroups have intersection exactly the identity. -/
theorem rankOne_level_iInter :
    (⋂ a : ℕ, (levelSubgroup F 0 a :
      Set (GeneralLinearGroup (Fin 1) F))) = {1} := by
  ext g
  constructor
  · intro hg
    have hg0 := Set.mem_iInter.mp hg 0
    rw [levelSubgroup_zero] at hg0
    obtain ⟨h, rfl⟩ := hg0
    have hh : h = 1 := by
      apply Set.mem_singleton_iff.mp
      rw [← rankOne_integral_iInter]
      apply Set.mem_iInter.mpr
      intro a
      exact (map_mem_congruenceSubgroup _ 0 _ h).1 (Set.mem_iInter.mp hg a)
    simp [hh]
  · rintro rfl
    exact Set.mem_iInter.mpr fun a => (levelSubgroup F 0 a).one_mem

/-- In rank one every neighborhood of the identity contains a level subgroup. -/
theorem rankOne_level_cofinal {U : Set (GeneralLinearGroup (Fin 1) F)}
    (hU : U ∈ 𝓝 (1 : GeneralLinearGroup (Fin 1) F)) :
    ∃ a : ℕ, (levelSubgroup F 0 a : Set (GeneralLinearGroup (Fin 1) F)) ⊆ U := by
  apply exists_subset_nhds_of_isCompact'
    (V := fun a => (levelSubgroup F 0 a : Set (GeneralLinearGroup (Fin 1) F)))
  · intro a b
    exact ⟨max a b, levelSubgroup_antitone F 0 (le_max_left _ _),
      levelSubgroup_antitone F 0 (le_max_right _ _)⟩
  · intro a
    exact isCompact_levelOpenSubgroup F 0 a
  · intro a
    exact (levelSubgroup F 0 a).isClosed_of_isOpen (levelOpenSubgroup F 0 a).isOpen'
  · simpa only [rankOne_level_iInter, nhdsSet_singleton] using hU

variable {K : Type uK} [CommRing K] {V : Type uV}
  [AddCommGroup V] [Module K V] [Nontrivial V]

/-- Smoothness supplies the finite-level existence prerequisite in rank one. -/
theorem hasNewvectorLevel_rankOne
    (ρ : Representation K (GeneralLinearGroup (Fin 1) F) V)
    (hρ : Langlands.IsSmooth ρ) : HasNewvectorLevel ρ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨J, hJ⟩ := hρ v
  obtain ⟨a, ha⟩ := rankOne_level_cofinal F (J.isOpen'.mem_nhds J.one_mem)
  refine ⟨a, ?_⟩
  have hfix : v ∈ levelFixedVectors ρ a :=
    (mem_levelFixedVectors ρ a v).2 fun g hg => hJ ⟨g, ha hg⟩
  intro hz
  rw [hz] at hfix
  exact hv hfix

/-- The finite first fixed level of an actual nonzero smooth rank-one action,
with existence proved from its topology. -/
def rankOneConductor
    (ρ : Representation K (GeneralLinearGroup (Fin 1) F) V)
    (hρ : Langlands.IsSmooth ρ) : ℕ :=
  newvectorConductor ρ (hasNewvectorLevel_rankOne F ρ hρ)

/-- An actual nonzero vector at the first fixed level in rank one. -/
def rankOneNewvector
    (ρ : Representation K (GeneralLinearGroup (Fin 1) F) V)
    (hρ : Langlands.IsSmooth ρ) :
    {v : V // v ∈ levelFixedVectors ρ (rankOneConductor F ρ hρ) ∧ v ≠ 0} :=
  newvector ρ (hasNewvectorLevel_rankOne F ρ hρ)

end Langlands.Conductor
