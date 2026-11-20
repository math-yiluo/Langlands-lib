import Langlands.BushnellKutzko.AdjointExactnessProof
import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.RelativeFiltrationInversion
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Exactness consequences for a single element generating a normalized field -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uE uV

section ElementExactness

variable {E : Type uE} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  {V : Type uV} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  (𝓛 : LatticeChain 𝒪[E] E V) (c : Module.End E V)

/-- The element `c` as a generator of its generated algebra `E[c]`. -/
def elementGenerator : elementAlgebra c :=
  ⟨c, Algebra.self_mem_adjoin_singleton E c⟩

theorem adjoin_elementGenerator :
    Algebra.adjoin E ({elementGenerator c} : Set (elementAlgebra c)) = ⊤ := by
  apply Subalgebra.map_injective (f := (elementAlgebra c).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, Set.image_singleton]
  rfl

theorem commute_of_elementAlgebra_eq_bot (hbot : elementAlgebra c = ⊥)
    (x : Module.End E V) : c * x - x * c = 0 := by
  have hc : c ∈ (⊥ : Subalgebra E (Module.End E V)) :=
    hbot ▸ Algebra.self_mem_adjoin_singleton E c
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hc
  rw [Algebra.commutes, sub_self]

theorem not_exists_algebraMap_elementGenerator (hbot : elementAlgebra c ≠ ⊥) :
    ¬ ∃ a : E, algebraMap E (elementAlgebra c) a = elementGenerator c := by
  rintro ⟨a, ha⟩
  apply hbot
  apply le_bot_iff.mp
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  have h := congrArg Subtype.val ha
  exact Algebra.mem_bot.mpr ⟨a, h⟩

variable (hfield : IsField (elementAlgebra c))

theorem subfieldEmbedding_elementGenerator :
    letI := hfield.toField
    subfieldEmbedding E (elementAlgebra c) V (elementGenerator c) = c := by
  letI := hfield.toField
  ext v
  rfl

variable (hnorm : letI := hfield.toField
  ∀ a : (elementAlgebra c)ˣ, subfieldUnits E (elementAlgebra c) V a ∈ 𝓛.stabilizer)
include hnorm

/-- The critical exponent of a nonscalar normalized field generator is the greatest critical
index. -/
theorem exists_isGreatest_criticalIndexSet (hbot : elementAlgebra c ≠ ⊥) :
    ∃ k₀ : ℤ, IsGreatest (criticalIndexSet 𝓛 c) k₀ ∧
      criticalExponent 𝓛 c = (k₀ : WithBot ℤ) := by
  letI := hfield.toField
  have h := adjointExactness E V (elementAlgebra c) 𝓛 (elementGenerator c)
    (adjoin_elementGenerator c) (not_exists_algebraMap_elementGenerator c hbot) hnorm
  rw [subfieldEmbedding_elementGenerator c hfield] at h
  exact h.2.2.2.1

/-- Middle exactness of the third sequence: if `k₀(c) ≤ k` and `[c, γ] ∈ 𝔓^{m+k}`, then there is
`γ₁` commuting with `c` with `γ - γ₁ ∈ 𝔓^m`. Exactness supplies the small endomorphism
`x = γ - γ₁ ∈ 𝔔^m 𝔑_k ⊆ 𝔓^m`, which has the same commutator with `c` as `γ`. -/
theorem exists_commute_sub_mem {k : ℤ} (hk : criticalExponent 𝓛 c ≤ (k : WithBot ℤ))
    (m : ℤ) (γ : Module.End E V) (hγ : c * γ - γ * c ∈ 𝓛.endFiltration (m + k)) :
    ∃ γ₁ : Module.End E V, c * γ₁ - γ₁ * c = 0 ∧ γ - γ₁ ∈ 𝓛.endFiltration m := by
  by_cases hbot : elementAlgebra c = ⊥
  · exact ⟨γ, commute_of_elementAlgebra_eq_bot c hbot γ, by
      rw [sub_self]; exact zero_mem _⟩
  letI := hfield.toField
  have h := adjointExactness E V (elementAlgebra c) 𝓛 (elementGenerator c)
    (adjoin_elementGenerator c) (not_exists_algebraMap_elementGenerator c hbot) hnorm
  rw [subfieldEmbedding_elementGenerator c hfield] at h
  obtain ⟨s⟩ := (tameCorestriction E V (elementAlgebra c)).1
  have h3 := (h.2.2.2.2 s m k 1 hk le_rfl).2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hmid⟩ := h3
  have hs : (s (adjointMap 𝒪[E] c γ)).restrictScalars E ∈
      (⊥ : Submodule 𝒪[E] (Module.End E V)).toAddSubgroup := by
    have h0 := s.adjointMap_eq_zero (elementGenerator c) γ
    rw [subfieldEmbedding_elementGenerator c hfield] at h0
    change (s (adjointMap 𝒪[E] c γ)).restrictScalars E = 0
    rw [show (adjointMap 𝒪[E] c γ) = adjointMap E c γ from rfl, h0]
    rfl
  obtain ⟨x, hx, hax⟩ := (hmid (adjointMap 𝒪[E] c γ) hγ).mp hs
  have hax' : c * γ - γ * c - (c * x - x * c) = 0 := hax
  refine ⟨γ - x, ?_, ?_⟩
  · rw [← sub_eq_zero.mpr (sub_eq_zero.mp hax')]
    noncomm_ring
  · rw [sub_sub_cancel]
    have hle : centralizerLattice 𝓛 c m * adjointLattice 𝓛 c k ≤ 𝓛.endFiltration m := by
      rw [Submodule.mul_le]
      intro q hq n hn
      simpa only [add_zero] using 𝓛.mul_mem_endFiltration hq.1 hn.1
    exact hle hx

/-- A nonscalar normalized field generator lying in `𝔓^r` has `r` as a critical index. -/
theorem mem_criticalIndexSet_of_mem (hbot : elementAlgebra c ≠ ⊥) {r : ℤ}
    (hc : c ∈ 𝓛.endFiltration r) : r ∈ criticalIndexSet 𝓛 c := by
  letI := hfield.toField
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hclear := 𝓛.exists_uniformizer_pow_mem_endFiltration hϖ
  have hperiod := 𝓛.maximalIdeal_smul_endFiltration_zero hϖ
  have hinv := one_mem_centralizerLattice_mul_neg 𝓛 hϖ (elementGenerator c) hnorm
  rw [subfieldEmbedding_elementGenerator c hfield] at hinv
  intro h
  have hN : 𝓛.endFiltration 0 ≤ adjointLattice 𝓛 c r := by
    intro x hx
    refine ⟨hx, ?_⟩
    change c * x - x * c ∈ 𝓛.endFiltration r
    exact sub_mem (by simpa using 𝓛.mul_mem_endFiltration hc hx)
      (by simpa using 𝓛.mul_mem_endFiltration hx hc)
  have hne : (ϖ : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have ha := adjointMap_eq_zero_of_order_le 𝓛 c hinv hne (fun x => hclear x 0) hperiod
    (hN.trans h)
  have hcenter : c ∈ Subalgebra.center E (Module.End E V) :=
    Subalgebra.mem_center_iff.mpr fun x => by
      have hzero := LinearMap.congr_fun ha x
      exact (sub_eq_zero.mp hzero).symm
  rw [Algebra.IsCentral.center_eq_bot] at hcenter
  exact hbot (le_bot_iff.mp (Algebra.adjoin_le fun x hx =>
    Set.mem_singleton_iff.mp hx ▸ hcenter))

end ElementExactness

end Langlands.BushnellKutzko
