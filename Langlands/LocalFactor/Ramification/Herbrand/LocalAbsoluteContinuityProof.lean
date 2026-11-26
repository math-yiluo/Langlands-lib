import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteStatement

/-!
# Left continuity of absolute upper ramification

The finite upper group is constant immediately to the left of each index
greater than `-1`. This yields left continuity of the absolute filtration
by testing membership after restriction to each finite Galois subextension.
-/

namespace Langlands.Ramification.Local

open Topology

universe u₀ uK uL uΩ

/-- At a finite level, an index strictly to the left of `v` has the same upper group. -/
private theorem exists_lt_upperRamificationGroup_eq
    {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
    {L : Type uL} [Field L] [Algebra K₀ L] [FiniteDimensional K₀ L]
    (T : LocalField.TopologicalData K₀ L)
    (K : Type uK) [Field K] [Algebra K₀ K] [Algebra K L] [IsScalarTower K₀ K L]
    {v : ℝ} (hv : -1 < v) :
    ∃ w : ℝ, -1 < w ∧ w < v ∧
      upperRamificationGroup T K w = upperRamificationGroup T K v := by
  let n := ⌈herbrandPsi T K v⌉
  have hn : (n : ℝ) - 1 < herbrandPsi T K v :=
    sub_lt_iff_lt_add.mpr (Int.ceil_lt_add_one _)
  have hPsi : ∀ᶠ w in 𝓝[<] v, (n : ℝ) - 1 < herbrandPsi T K w :=
    mem_nhdsWithin_of_mem_nhds
      (((herbrandPsi_continuous T K).tendsto v).eventually (lt_mem_nhds hn))
  have hAbove : ∀ᶠ w in 𝓝[<] v, -1 < w :=
    mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hv)
  have hBelow : ∀ᶠ w in 𝓝[<] v, w < v := self_mem_nhdsWithin
  obtain ⟨w, hwPsi, hw, hwv⟩ := (hPsi.and (hAbove.and hBelow)).exists
  have hceil : ⌈herbrandPsi T K w⌉ = ⌈herbrandPsi T K v⌉ :=
    Int.ceil_eq_iff.mpr ⟨hwPsi, (herbrandPsi_strictMono T K hwv).le.trans (Int.le_ceil _)⟩
  refine ⟨w, hw, hwv, ?_⟩
  simp only [upperRamificationGroup_eq_lower, hceil]

/-- Left continuity of the absolute upper filtration inside Serre's domain. -/
theorem absoluteUpperLeftContinuity
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] :
    AbsoluteUpperLeftContinuity K Ω := by
  intro v hv
  apply le_antisymm
  · exact le_iInf₂ fun w hw => localAbsoluteUpperRamificationGroup_antitone K Ω hw.2.le
  · intro σ hσ
    simp only [Subgroup.mem_iInf, localAbsoluteUpperRamificationGroup,
      mem_absoluteUpperRamificationGroup_iff] at hσ ⊢
    intro L
    obtain ⟨w, hw, hwv, heq⟩ := exists_lt_upperRamificationGroup_eq
      (localTopologicalData K L) K hv
    change absoluteFiniteRestriction K Ω L σ ∈
      upperRamificationGroup (localTopologicalData K L) K v
    rw [← heq]
    exact hσ w ⟨hw.le, hwv⟩ L

end Langlands.Ramification.Local
