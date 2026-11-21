import Langlands.Analysis.SliceJetEstimates
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.Support

/-! # A distribution supported on a slice depends on a finite jet -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped ContDiff Distributions NNReal

namespace Langlands.Analysis

universe uX uY uV

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A distribution's restriction to a fixed compact support has finite derivative order. -/
theorem exists_distribution_compact_bound {Ω : Opens X} (T : 𝓓'(Ω, V)) (K : Compacts X)
    (hK : (K : Set X) ⊆ Ω) :
    ∃ (S : Finset ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓓_{K}(X, ℝ),
      ‖T (TestFunction.ofSupportedIn hK f)‖ ≤
        C * ∑ i ∈ S, ContDiffMapSupportedIn.seminorm ℝ X ℝ ⊤ K i f := by
  let L : 𝓓_{K}(X, ℝ) →L[ℝ] V :=
    (show 𝓓(Ω, ℝ) →L[ℝ] V from T).comp (TestFunction.ofSupportedInCLM ℝ hK)
  let q : Seminorm ℝ 𝓓_{K}(X, ℝ) := (normSeminorm ℝ V).comp L.toLinearMap
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ X ℝ ⊤ K) q (continuous_norm.comp L.continuous)
  refine ⟨S, C, C.coe_nonneg, fun f => ?_⟩
  have h := Seminorm.le_def.mp hC f
  rw [smul_apply, NNReal.smul_def, smul_eq_mul] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
  exact Seminorm.finset_sup_apply_le
    (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) (fun i hi =>
      Finset.single_le_sum (fun _ _ => apply_nonneg _ _) hi)

/-- On each fixed compact support, a distribution supported on the
zero slice annihilates tests whose full jet through some finite order
vanishes on that slice. -/
theorem exists_order_annihilate_flat_on_slice [FiniteDimensional ℝ Y]
    {Ω : Opens (X × Y)} (T : 𝓓'(Ω, V))
    (hT : Distribution.IsVanishingOn T {p : X × Y | p.2 ≠ 0})
    (K : Compacts (X × Y)) (hK : (K : Set (X × Y)) ⊆ Ω) :
    ∃ m : ℕ, ∀ f : 𝓓_{K}(X × Y, ℝ),
      (∀ x : X, ∀ j ≤ m, iteratedFDeriv ℝ j f (x, (0 : Y)) = 0) →
      T (TestFunction.ofSupportedIn hK f) = 0 := by
  obtain ⟨S, C, hC, hbound⟩ := exists_distribution_compact_bound T K hK
  let m := S.sup id
  have hm (i : ℕ) (hi : i ∈ S) : i ≤ m := Finset.le_sup (f := id) hi
  refine ⟨m, fun f hflat => ?_⟩
  let b : ContDiffBump (0 : Y) :=
    ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hbs : tsupport (b : Y → ℝ) ⊆ closedBall (0 : Y) 1 := by
    rw [b.tsupport_eq]
  obtain ⟨A, hA, hcut⟩ := exists_norm_iteratedFDeriv_normalCutoff_le
    f.contDiff f.compact_supp b.contDiff b.hasCompactSupport hbs m hflat
  have hsmall (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) :
      ‖T (TestFunction.ofSupportedIn hK f)‖ ≤ (C * ∑ i ∈ S, A i) * ε := by
    let g : 𝓓_{K}(X × Y, ℝ) :=
      ⟨fun p => b (ε⁻¹ • p.2) • f p,
        (b.contDiff.comp (contDiff_const.smul contDiff_snd)).smul f.contDiff,
        fun p hp => by
          change b (ε⁻¹ • p.2) • f p = 0
          have hfp : f p = 0 := f.zero_on_compl hp
          rw [hfp, smul_zero]⟩
    have hfg : tsupport (f - g : 𝓓_{K}(X × Y, ℝ)) ⊆ {p : X × Y | p.2 ≠ 0} := by
      have hclosed : IsClosed {p : X × Y | ε / 2 ≤ ‖p.2‖} :=
        isClosed_le continuous_const continuous_snd.norm
      refine (closure_minimal ?_ hclosed).trans ?_
      · intro p hp
        by_contra! hp'
        change ¬ ε / 2 ≤ ‖p.2‖ at hp'
        have hb : b (ε⁻¹ • p.2) = 1 := by
          apply b.one_of_mem_closedBall
          rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
          apply (inv_mul_le_iff₀ hε).2
          change ‖p.2‖ ≤ ε * (1 / 2)
          linarith
        apply hp
        change f p - b (ε⁻¹ • p.2) • f p = 0
        rw [hb, one_smul, sub_self]
      · intro p hp he
        change ε / 2 ≤ ‖p.2‖ at hp
        rw [he, norm_zero] at hp
        linarith
    have hsame : T (TestFunction.ofSupportedIn hK f) = T (TestFunction.ofSupportedIn hK g) := by
      let L : 𝓓_{K}(X × Y, ℝ) →L[ℝ] V :=
        (show 𝓓(Ω, ℝ) →L[ℝ] V from T).comp (TestFunction.ofSupportedInCLM ℝ hK)
      have hzero : L (f - g) = 0 := hT (TestFunction.ofSupportedIn hK (f - g)) hfg
      rw [map_sub, sub_eq_zero] at hzero
      exact hzero
    rw [hsame]
    calc
      _ ≤ C * ∑ i ∈ S, ContDiffMapSupportedIn.seminorm ℝ (X × Y) ℝ ⊤ K i g := hbound g
      _ ≤ C * ∑ i ∈ S, A i * ε := by
        apply mul_le_mul_of_nonneg_left _ hC
        refine Finset.sum_le_sum fun i hi => ?_
        exact (g.seminorm_top_le_iff ℝ (mul_nonneg (hA i) hε.le) i).2
          (fun p _ => hcut ε hε hε₁ i (hm i hi) p)
      _ = _ := by rw [← Finset.sum_mul, mul_assoc]
  let B := C * ∑ i ∈ S, A i
  have hB : 0 ≤ B := mul_nonneg hC (Finset.sum_nonneg fun i _ => hA i)
  apply norm_eq_zero.mp
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (norm_nonneg _)
  have hB₁ : 0 < B + 1 := by linarith
  let ε := min 1 (δ / (B + 1))
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hδ hB₁)
  calc
    _ ≤ B * ε := hsmall ε hε (min_le_left _ _)
    _ ≤ (B + 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
    _ ≤ (B + 1) * (δ / (B + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hB₁.le
    _ = 0 + δ := by field_simp [ne_of_gt hB₁]; ring

end Langlands.Analysis
