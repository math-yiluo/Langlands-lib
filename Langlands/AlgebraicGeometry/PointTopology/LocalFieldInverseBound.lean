import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # A compact set containing every element or its inverse -/

noncomputable section
universe u

open Filter Topology Set Pointwise

namespace Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]

/-- A nondiscrete Hausdorff locally compact topological field has a nonzero topologically
nilpotent element. -/
theorem exists_ne_zero_tendsto_pow_zero [T2Space K] [LocallyCompactSpace K]
    (hnd : ¬ DiscreteTopology K) :
    ∃ t : K, t ≠ 0 ∧ Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0) := by
  obtain ⟨V, hVc, hV0⟩ := exists_compact_mem_nhds (0 : K)
  have h1 : ({1}ᶜ : Set K) ∈ 𝓝 (0 : K) :=
    isOpen_compl_singleton.mem_nhds (by simp)
  obtain ⟨F, hF0, hFc, hFV⟩ := exists_mem_nhds_isClosed_subset (inter_mem hV0 h1)
  have hW : ∀ᶠ w in 𝓝 (0 : K), ∀ v ∈ V, w * v ∈ F := by
    refine hVc.eventually_forall_of_forall_eventually fun v _ => ?_
    have : Tendsto (fun z : K × K => z.1 * z.2) (𝓝 (0, v)) (𝓝 (0 * v)) :=
      continuous_mul.tendsto _
    rw [zero_mul] at this
    exact this hF0
  have hne : ∀ s ∈ 𝓝 (0 : K), ∃ t ∈ s, t ≠ 0 := by
    intro s hs
    by_contra hcon
    push Not at hcon
    apply hnd
    rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_singleton_iff_nhds_eq_pure]
    exact le_antisymm (le_pure_iff.mpr (mem_of_superset hs fun t ht => hcon t ht))
      (pure_le_nhds 0)
  obtain ⟨t, ⟨htV, htW⟩, ht0⟩ := hne _ (inter_mem hV0 hW)
  have hpowV : ∀ n : ℕ, t ^ (n + 1) ∈ V := by
    intro n
    induction n with
    | zero => simpa using htV
    | succ n ih => rw [pow_succ']; exact (hFV (htW _ ih)).1
  have hpowF : ∀ n : ℕ, t ^ (n + 2) ∈ F := by
    intro n
    rw [pow_succ']
    exact htW _ (hpowV n)
  refine ⟨t, ht0, hVc.tendsto_nhds_of_unique_mapClusterPt ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [Nat.sub_add_cancel hn] using hpowV (n - 1)
  · intro b _ hb
    by_contra hb0
    have h1F : (Fᶜ : Set K) ∈ 𝓝 (1 : K) :=
      hFc.isOpen_compl.mem_nhds fun h => (hFV h).2 rfl
    have hcont : Tendsto (fun z : K × K => z.1 * z.2⁻¹) (𝓝 (b, b)) (𝓝 1) := by
      have : ContinuousAt (fun z : K × K => z.1 * z.2⁻¹) (b, b) :=
        continuousAt_fst.mul ((continuousAt_inv₀ hb0).comp continuousAt_snd)
      simpa [ContinuousAt, mul_inv_cancel₀ hb0] using this
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hcont h1F)
    have hfreq := (mapClusterPt_iff_frequently.mp hb) (u ∩ v) (inter_mem hu hv)
    rw [frequently_atTop] at hfreq
    obtain ⟨n, -, hn⟩ := hfreq 0
    obtain ⟨m, hm, hm'⟩ := hfreq (n + 2)
    have hmem : t ^ m * (t ^ n)⁻¹ ∈ Fᶜ := huv (mk_mem_prod hm'.1 hn.2)
    rw [← pow_sub₀ t ht0 (by omega : n ≤ m)] at hmem
    obtain ⟨j, hj⟩ : ∃ j, m - n = j + 2 := ⟨m - n - 2, by omega⟩
    exact hmem (hj ▸ hpowF j)

/-- A nondiscrete Hausdorff locally compact topological field has a compact subset containing,
for every element, the element or its inverse. -/
theorem exists_isCompact_mem_or_inv_mem [T2Space K] [LocallyCompactSpace K]
    (hnd : ¬ DiscreteTopology K) :
    ∃ C : Set K, IsCompact C ∧ ∀ x : K, x ∈ C ∨ x⁻¹ ∈ C := by
  obtain ⟨t, ht0, htlim⟩ := exists_ne_zero_tendsto_pow_zero hnd
  obtain ⟨V, hVc, hV0⟩ := exists_compact_mem_nhds (0 : K)
  set A : Set K := V ∩ Homeomorph.mulLeft₀ t ht0 '' (interior V)ᶜ with hAdef
  have hAc : IsCompact A :=
    hVc.inter_right ((Homeomorph.mulLeft₀ t ht0).isClosedMap _ isOpen_interior.isClosed_compl)
  have hA0 : (0 : K) ∉ A := by
    rintro ⟨_, y, hy, hty⟩
    have hy0 : y = 0 := by simpa [ht0] using hty
    exact hy (hy0 ▸ mem_interior_iff_mem_nhds.2 hV0)
  have hAinv : IsCompact A⁻¹ := by
    rw [← image_inv_eq_inv]
    exact hAc.image_of_continuousOn fun a ha =>
      (continuousAt_inv₀ fun h => hA0 (h ▸ ha)).continuousWithinAt
  set T : Set K := insert 0 (range fun n : ℕ => t ^ (n + 1)) with hTdef
  have hT : IsCompact T := (htlim.comp (tendsto_add_atTop_nat 1)).isCompact_insert_range
  refine ⟨V ∪ T * A⁻¹, hVc.union (hT.mul hAinv), fun x => ?_⟩
  by_cases hx : x ∈ V
  · exact Or.inl (Or.inl hx)
  right; right
  have hex : ∃ n : ℕ, t ^ n * x ∈ V := by
    have : Tendsto (fun n : ℕ => t ^ n * x) atTop (𝓝 0) := by
      simpa using htlim.mul_const x
    exact (this.eventually hV0).exists
  classical
  have hk : t ^ Nat.find hex * x ∈ V := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    apply hx
    simpa [h] using hk
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  have hj' : t ^ j * x ∉ V := Nat.find_min hex (by omega)
  have hu : t ^ Nat.find hex * x ∈ A := by
    refine ⟨hk, t ^ j * x, fun h => hj' (interior_subset h), ?_⟩
    simp only [Homeomorph.coe_mulLeft₀, hj, pow_succ]
    ring
  refine ⟨t ^ Nat.find hex, Or.inr ⟨j, by rw [hj]⟩, (t ^ Nat.find hex * x)⁻¹,
    by simpa using hu, ?_⟩
  simp only [mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0), one_mul]

end Langlands.AlgebraicGeometry.PointTopology
