import Mathlib.Analysis.Distribution.Support
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

/-! # Local vanishing and support descent for smooth distributions -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions Manifold

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E}

/-- Pointwise multiplication by a fixed smooth scalar function on a test space. -/
def smoothScalarMultiplierCLM {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.limitCLM ℝ
    (fun f => ⟨fun x => f x * χ x, f.contDiff.mul hχ, f.hasCompactSupport.mul_right,
      tsupport_mul_subset_left.trans f.tsupport_subset⟩)
    (fun _ hK => (TestFunction.ofSupportedInCLM ℝ hK).comp
      (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hχ))
    (fun _ _ _ => rfl)

@[simp]
theorem smoothScalarMultiplierCLM_apply {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (f : 𝓓(Ω, ℝ)) (x : E) : smoothScalarMultiplierCLM hχ f x = f x * χ x := rfl

/-- Vanishing on each open in a family implies vanishing on their union. -/
theorem smoothDistribution_isVanishingOn_iUnion [FiniteDimensional ℝ E] {ι : Type*}
    (T : 𝓓'(Ω, F)) (s : ι → Set E) (ho : ∀ i, IsOpen (s i))
    (hs : ∀ i, Distribution.IsVanishingOn T (s i)) :
    Distribution.IsVanishingOn T (⋃ i, s i) := by
  classical
  intro f hf
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E))
    (isClosed_tsupport f) s ho hf
  let t (i : ι) : 𝓓(Ω, ℝ) := smoothScalarMultiplierCLM (ρ i).contMDiff.contDiff f
  have ht (i : ι) : T (t i) = 0 := hs i (t i) (tsupport_mul_subset_right.trans (hρ i))
  have hfinite := ρ.locallyFinite.finite_nonempty_inter_compact f.hasCompactSupport
  let I := hfinite.toFinset
  have hsum : (∑ i ∈ I, t i) = f := by
    ext x
    change (FunLike.coeAddMonoidHom 𝓓(Ω, ℝ) E ℝ (∑ i ∈ I, t i)) x = f x
    rw [map_sum, Finset.sum_apply]
    change (∑ i ∈ I, f x * ρ i x) = f x
    by_cases hx : x ∈ tsupport f
    · have hI : ρ.finsupport x ⊆ I := by
        intro i hi
        have hix : x ∈ Function.support (ρ i) := (ρ.mem_finsupport x).mp hi
        exact hfinite.mem_toFinset.mpr ⟨x, hix, hx⟩
      rw [← Finset.mul_sum, ρ.sum_finsupport' x hx hI, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => ht i

/-- A smooth distribution vanishes on the entire open complement of its support. -/
theorem smoothDistribution_isVanishingOn_compl_dsupport [FiniteDimensional ℝ E]
    (T : 𝓓'(Ω, F)) : Distribution.IsVanishingOn T (Distribution.dsupport T)ᶜ := by
  rw [Distribution.dsupport_compl_eq, Set.sUnion_eq_iUnion]
  exact smoothDistribution_isVanishingOn_iUnion T _ (fun s => s.property.2)
    (fun s => s.property.1)

theorem smoothDistribution_eq_zero_of_dsupport_eq_empty [FiniteDimensional ℝ E]
    (T : 𝓓'(Ω, F)) (h : Distribution.dsupport T = ∅) : T = 0 := by
  have hv := smoothDistribution_isVanishingOn_compl_dsupport T
  rw [h, compl_empty] at hv
  apply DFunLike.ext
  intro f
  exact hv f (subset_univ _)

/-- To eliminate a part of the putative support, it is enough to prove
vanishing in an open neighborhood of each point of that part. -/
theorem smoothDistribution_dsupport_subset_of_local_vanishing
    (T : 𝓓'(Ω, F)) {s t : Set E}
    (hs : Distribution.dsupport T ⊆ s)
    (h : ∀ x ∈ s \ t, ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ Distribution.IsVanishingOn T u) :
    Distribution.dsupport T ⊆ t := by
  intro x hx
  by_contra hxt
  obtain ⟨u, hu, hxu, hv⟩ := h x ⟨hs hx, hxt⟩
  exact (Distribution.notMem_dsupport_iff _).mpr ⟨u, hv, hu, hxu⟩ hx

/-- Successive local vanishing on a finite filtration with empty last term
implies that the distribution is zero. -/
theorem smoothDistribution_eq_zero_of_support_descent [FiniteDimensional ℝ E]
    (T : 𝓓'(Ω, F)) (s : ℕ → Set E) (m : ℕ)
    (h0 : Distribution.dsupport T ⊆ s 0) (hm : s m = ∅)
    (hstep : ∀ i < m, Distribution.dsupport T ⊆ s i →
      ∀ x ∈ s i \ s (i + 1), ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ Distribution.IsVanishingOn T u) :
    T = 0 := by
  have hsub (k : ℕ) (hk : k ≤ m) : Distribution.dsupport T ⊆ s k := by
    induction k with
    | zero => exact h0
    | succ k ih =>
      have h := ih (Nat.le_of_succ_le hk)
      exact smoothDistribution_dsupport_subset_of_local_vanishing T h
        (hstep k (Nat.lt_of_succ_le hk) h)
  exact smoothDistribution_eq_zero_of_dsupport_eq_empty T
    (subset_empty_iff.mp (hm ▸ hsub m le_rfl))

end Langlands.HarmonicAnalysis
