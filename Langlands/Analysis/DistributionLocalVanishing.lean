import Mathlib.Analysis.Distribution.Support
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Local vanishing implies vanishing on tests supported in the union -/

noncomputable section
set_option autoImplicit false

open Function Set TopologicalSpace
open scoped ContDiff Distributions Manifold

namespace Langlands.Analysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

/-- A complex distribution vanishes on tests supported in `U` if it
vanishes on some open neighborhood of each point of `U`. -/
theorem isVanishingOn_of_locallyVanishing (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) {U : Set E}
    (hU : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ Distribution.IsVanishingOn T V) :
    Distribution.IsVanishingOn T U := by
  classical
  intro f hf
  let K := tsupport f
  have h (x : K) : ∃ V : Set E, IsOpen V ∧ x.val ∈ V ∧ Distribution.IsVanishingOn T V :=
    hU x.val (hf x.property)
  choose V hVo hVx hVT using h
  have hCover : K ⊆ ⋃ x : K, V x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩
  obtain ⟨J, hJ⟩ := f.hasCompactSupport.elim_finite_subcover V hVo hCover
  have hCover' : K ⊆ ⋃ j : J, V j.val := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hix⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, E))
    (isClosed_tsupport f) (fun j : J => V j.val) (fun j => hVo j.val) hCover'
  let g (j : J) : 𝓓(Ω, ℂ) :=
    ⟨fun x => ρ j x • f x, ((contMDiff_iff_contDiff.mp (ρ j).contMDiff).smul f.contDiff),
      f.hasCompactSupport.of_isClosed_subset isClosed_closure (tsupport_smul_subset_right _ _),
      (tsupport_smul_subset_right _ _).trans f.tsupport_subset⟩
  have hzero (j : J) : T (g j) = 0 :=
    hVT j.val (g j) ((tsupport_smul_subset_left _ _).trans (hρ j))
  have hsum : (∑ j : J, g j) = f := by
    apply TestFunction.ext
    intro x
    let eval : 𝓓(Ω, ℂ) →+ ℂ :=
      { toFun := fun h => h x
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change eval (∑ j : J, g j) = f x
    rw [map_sum]
    change (∑ j : J, ρ j x • f x) = f x
    by_cases hx : x ∈ K
    · have hρ₁ : (∑ j : J, ρ j x) = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [← Finset.sum_smul, hρ₁, one_smul]
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz]
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero fun j _ => hzero j

end Langlands.Analysis
