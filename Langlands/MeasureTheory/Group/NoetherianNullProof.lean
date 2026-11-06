import Langlands.MeasureTheory.Group.NoetherianNullStatement

/-! # Noetherian induction for null closed inverse images -/

noncomputable section

universe u v

open MeasureTheory TopologicalSpace Filter Topology
open scoped Pointwise

namespace Langlands.MeasureTheory

/-- The complete Noetherian closed-set nullness statement. -/
theorem noetherianClosedNull : NoetherianClosedNullStatement.{u, v} := by
  intro H _ _ _ _ _ _ _ X _ _ μ _ _ _ f hf e he hd Z
  apply wellFounded_lt.induction Z
  clear Z
  intro Z ih hZ
  by_contra hnull
  obtain ⟨K, hKZ, hK, hKpos⟩ :=
    (Z.isClosed.preimage hf).measurableSet.exists_lt_isCompact (pos_iff_ne_zero.mpr hnull)
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hKpos.ne'
  have hnear : ∀ᶠ g in 𝓝 (1 : H), μ (g • K \ K) < μ K :=
    eventually_nhds_one_measure_smul_sdiff_lt hK hK.isClosed hKpos.ne'
  have hcont : Tendsto (fun y : H => x * y⁻¹) (𝓝 x) (𝓝 (1 : H)) := by
    have hc : ContinuousAt (fun y : H => x * y⁻¹) x :=
      continuousAt_const.mul continuousAt_id.inv
    change Tendsto (fun y : H => x * y⁻¹) (𝓝 x) (𝓝 (x * x⁻¹)) at hc
    simpa only [mul_inv_cancel] using hc
  have hnearx : {y : H | μ ((x * y⁻¹) • K \ K) < μ K} ∈ 𝓝 x := by
    exact hcont.eventually hnear
  obtain ⟨y, hy, hynear⟩ :=
    (interior_eq_empty_iff_dense_compl.mp (hd Z hZ)).inter_nhds_nonempty hnearx
  let g : H := x * y⁻¹
  have hxy : g * y = x := by simp [g]
  let T : Closeds X := ⟨(e g).symm ⁻¹' (Z : Set X), Z.isClosed.preimage (e g).symm.continuous⟩
  have hxZ : f x ∈ Z := hKZ hx
  have hxT : f x ∉ T := by
    change (e g).symm (f x) ∉ Z
    have hexy : f x = e g (f y) := by rw [← hxy, he]
    rw [hexy, Homeomorph.symm_apply_apply]
    exact hy
  have hlt : Z ⊓ T < Z := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hz
    have hxZT : f x ∈ Z ⊓ T := by rw [hz]; exact hxZ
    exact hxT hxZT.2
  have hproper : Z ⊓ T ≠ ⊤ := by
    intro hz
    apply hZ
    exact top_le_iff.mp (hz ▸ (inf_le_left : Z ⊓ T ≤ Z))
  have hsmall := ih (Z ⊓ T) hlt hproper
  have hinter : μ (g • K ∩ K) = 0 := by
    apply measure_mono_null _ hsmall
    rintro z ⟨hz, hzK⟩
    refine ⟨hKZ hzK, ?_⟩
    obtain ⟨k, hk, rfl⟩ := hz
    change (e g).symm (f (g * k)) ∈ Z
    rw [he, Homeomorph.symm_apply_apply]
    exact hKZ hk
  have hdecomp := measure_inter_add_sdiff (μ := μ) (g • K) hK.isClosed.measurableSet
  rw [hinter, zero_add, measure_smul] at hdecomp
  exact (ne_of_lt hynear) hdecomp

end Langlands.MeasureTheory
