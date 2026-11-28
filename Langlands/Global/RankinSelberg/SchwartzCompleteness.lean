import Langlands.Global.RankinSelberg.SchwartzRapidMajorant
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Completeness of the Schwartz seminorm topology -/

noncomputable section

open Filter Set
open scoped SchwartzMap Topology Uniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzMajorant

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The sums of a series absolutely summable in every Schwartz seminorm converge
in the Schwartz topology. -/
theorem tendsto_schwartz_sum (f : ℕ → 𝓢(E, F))
    (hf : ∀ k n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ k n (f j))) :
    ∃ Φ : 𝓢(E, F), Tendsto (fun N => ∑ j ∈ Finset.range N, f j) atTop (𝓝 Φ) := by
  obtain ⟨Φ, hΦ, _⟩ := exists_schwartz_tsum_with_seminorm f hf
  refine ⟨Φ, ((schwartz_withSeminorms ℝ E F).tendsto_nhds _ _).2 ?_⟩
  intro i ε hε
  let p : Seminorm ℝ 𝓢(E, F) := SchwartzMap.seminorm ℝ i.1 i.2
  have hp (N : ℕ) : p ((∑ j ∈ Finset.range N, f j) - Φ) ≤ ∑' j, p (f (j + N)) := by
    obtain ⟨Ψ, hΨ, hBound⟩ := exists_schwartz_tsum_with_seminorm (fun j => f (j + N))
      (fun k n => (summable_nat_add_iff N).2 (hf k n))
    have he : Φ - (∑ j ∈ Finset.range N, f j) = Ψ := by
      ext x
      have hfx : Summable (fun j => f j x) :=
        (hf 0 0).of_norm_bounded fun j => (f j).norm_le_seminorm ℝ x
      change Φ x - (∑ j ∈ Finset.range N, f j) x = Ψ x
      have hEval : (∑ j ∈ Finset.range N, f j) x = ∑ j ∈ Finset.range N, f j x := sum_apply ..
      rw [hEval, hΦ, hΨ, ← hfx.sum_add_tsum_nat_add N, add_sub_cancel_left]
    rw [← map_neg_eq_map p, neg_sub, he]
    exact hBound i.1 i.2
  exact ((tendsto_sum_nat_add (f := fun j => p (f j))).eventually (gt_mem_nhds hε)).mono
    (fun N hN => (hp N).trans_lt hN)

/-- Schwartz functions valued in a complete real normed space are complete for the
Schwartz seminorm topology. -/
def SchwartzCompleteSpaceStatement : Prop := CompleteSpace 𝓢(E, F)

theorem schwartzCompleteSpace : SchwartzCompleteSpaceStatement E F := by
  let : (𝓤 (𝓢(E, F))).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let p := schwartzSeminormFamily ℝ E F
  let S (n : ℕ) : Finset (ℕ × ℕ) := Finset.Iic (n, n)
  let e (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
  let U (n : ℕ) : SetRel (𝓢(E, F)) (𝓢(E, F)) :=
    {xy | (S n).sup p (xy.2 - xy.1) < e n}
  have hU (n : ℕ) : U n ∈ 𝓤 (𝓢(E, F)) := by
    rw [uniformity_eq_comap_nhds_zero]
    have hz := (schwartz_withSeminorms ℝ E F).hasBasis_zero_ball.mem_of_mem
      (i := (S n, e n)) (show 0 < e n by dsimp [e]; positivity)
    rw [Seminorm.ball_zero_eq] at hz
    exact Filter.preimage_mem_comap hz
  apply UniformSpace.complete_of_convergent_controlled_sequences U hU
  intro u hu
  let f (n : ℕ) := u (n + 1) - u n
  have hf (k l : ℕ) : Summable (fun n => SchwartzMap.seminorm ℝ k l (f n)) := by
    let N := max k l
    apply (summable_nat_add_iff N).mp
    have he : Summable e := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine Summable.of_nonneg_of_le (fun _ => apply_nonneg _ _) ?_ ((summable_nat_add_iff N).mpr he)
    intro n
    have hs : (k, l) ∈ S (n + N) := Finset.mem_Iic.mpr (Prod.mk_le_mk.mpr (by dsimp [N]; omega))
    have hu' : (S (n + N)).sup p (f (n + N)) < e (n + N) := hu (n + N) (n + N) (n + N + 1) le_rfl (by omega)
    exact (Seminorm.le_def.mp (Finset.le_sup hs) (f (n + N))).trans hu'.le
  obtain ⟨Φ, hΦ⟩ := tendsto_schwartz_sum E F f hf
  refine ⟨Φ + u 0, ?_⟩
  have heq (N : ℕ) : (∑ j ∈ Finset.range N, f j) + u 0 = u N := by
    rw [show (∑ j ∈ Finset.range N, f j) = u N - u 0 from Finset.sum_range_sub u N, sub_add_cancel]
  simpa only [heq] using hΦ.add_const (u 0)

end Langlands.Global.RankinSelbergGlobal.SchwartzMajorant
