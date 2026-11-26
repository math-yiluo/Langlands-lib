import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

/-! # Smooth pullback with a fixed compactly supported weight -/

noncomputable section

open Function Seminorm Set TopologicalSpace WithSeminorms
open scoped ContDiff Distributions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_uniform_jet_bound {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E → V} (hf : ContDiff ℝ ∞ f) (K : Compacts E) (i : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x ∈ (K : Set E), ∀ j ≤ i, ‖iteratedFDeriv ℝ j f x‖ ≤ D := by
  have h (j : Fin (i + 1)) : ∃ B : ℝ, ∀ x ∈ (K : Set E),
      ‖iteratedFDeriv ℝ (j : ℕ) f x‖ ≤ B :=
    K.isCompact.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (m := (j : ℕ)) (by simp)).continuousOn
  choose B hB using h
  let D := 1 + ∑ j : Fin (i + 1), |B j|
  refine ⟨D, le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _), ?_⟩
  intro x hx j hj
  let l : Fin (i + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  exact (hB l x hx).trans <| (le_abs_self (B l)).trans <|
    (Finset.single_le_sum (f := fun l => |B l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)).trans
      (le_add_of_nonneg_left zero_le_one)

/-- Pull a fixed-support smooth test back along a smooth map and multiply it by a smooth
weight whose support is contained in the prescribed compact target support. -/
def compactWeightedTestPullback (K : Compacts E) (L : Compacts F) (p : E → F) (w : E → ℂ)
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hK : tsupport w ⊆ K) :
    𝓓_{L}(F, ℂ) →L[ℂ] 𝓓_{K}(E, ℂ) := by
  let P : 𝓓_{L}(F, ℂ) →ₗ[ℂ] 𝓓_{K}(E, ℂ) :=
    { toFun := fun f => ContDiffMapSupportedIn.of_support_subset (hw.mul (f.contDiff.comp hp))
        (fun x hx => by
          by_contra hn
          have hw0 := image_eq_zero_of_notMem_tsupport (fun hz => hn (hK hz))
          exact hx (show w x * f (p x) = 0 by rw [hw0, zero_mul]))
      map_add' := fun f g => ContDiffMapSupportedIn.ext fun x => by
        change w x * (f (p x) + g (p x)) = _
        exact mul_add _ _ _
      map_smul' := fun c f => ContDiffMapSupportedIn.ext fun x => by
        change w x * (c * f (p x)) = c * (w x * f (p x))
        rw [mul_left_comm] }
  refine ⟨P, continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ℂ F ℂ ⊤ L)
    (ContDiffMapSupportedIn.withSeminorms ℂ E ℂ ⊤ K) P (.of_real fun i => ?_)⟩
  obtain ⟨D, hD, hDp⟩ := exists_uniform_jet_bound hp K i
  obtain ⟨W, hW, hWw⟩ := exists_uniform_jet_bound hw K i
  let C := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * W * ((i - j).factorial * D ^ (i - j))
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨Finset.Iic i, C, fun f => ?_⟩
  let q := (Finset.Iic i).sup (fun j => ContDiffMapSupportedIn.seminorm ℂ F ℂ ⊤ L j)
  change ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K i (P f) ≤ C * q f
  refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (mul_nonneg hC (apply_nonneg _ _))
    i (P f)).mpr ?_
  intro x hx
  have hder (j : ℕ) (hj : j ≤ i) : ‖iteratedFDeriv ℝ j (f ∘ p) x‖ ≤
      j.factorial * q f * D ^ j := by
    apply norm_iteratedFDeriv_comp_le f.contDiff hp (by simp)
    · intro k hk
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
        (Finset.le_sup (f := fun l => ContDiffMapSupportedIn.seminorm ℂ F ℂ ⊤ L l)
          (Finset.mem_Iic.mpr (hk.trans hj)) f)
    · intro k hk hkj
      exact (hDp x hx k (hkj.trans hj)).trans (le_self_pow₀ hD (by omega))
  calc
    ‖iteratedFDeriv ℝ i (P f : E → ℂ) x‖ ≤ ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j w x‖ * ‖iteratedFDeriv ℝ (i - j) (f ∘ p) x‖ :=
      norm_iteratedFDeriv_mul_le hw (f.contDiff.comp hp) x (by simp)
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * W * ((i - j).factorial * q f * D ^ (i - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hw' := hWw x hx j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      have hp' := hder (i - j) (Nat.sub_le _ _)
      gcongr
    _ = C * q f := by
      unfold C
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem compactWeightedTestPullback_apply (K : Compacts E) (L : Compacts F)
    (p : E → F) (w : E → ℂ) (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hK : tsupport w ⊆ K)
    (f : 𝓓_{L}(F, ℂ)) (x : E) : compactWeightedTestPullback K L p w hp hw hK f x = w x * f (p x) :=
  rfl

/-- The weighted pullback on each fixed-support test space is continuous and complex linear. -/
def CompactWeightedTestPullbackStatement : Prop :=
  ∀ (K : Compacts E) (L : Compacts F) (p : E → F) (w : E → ℂ),
    ContDiff ℝ ∞ p → ContDiff ℝ ∞ w → tsupport w ⊆ K →
    ∃ P : 𝓓_{L}(F, ℂ) →L[ℂ] 𝓓_{K}(E, ℂ), ∀ f x, P f x = w x * f (p x)

theorem compactWeightedTestPullbackStatement : CompactWeightedTestPullbackStatement (E := E) (F := F) :=
  fun K L p w hp hw hK => ⟨compactWeightedTestPullback K L p w hp hw hK, fun _ _ => rfl⟩

end Langlands.Analysis
