import Langlands.Analysis.SmoothIteratedFDerivSymm
import Langlands.HarmonicAnalysis.Distribution.SmoothCompactOrder
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Flat tests for distributions supported on a coordinate subspace -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def transverseBump : ContDiffBump (0 : W) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

private def scaledProjection (t : ℝ) : E × W →L[ℝ] W :=
  t • ContinuousLinearMap.snd ℝ E W

omit [FiniteDimensional ℝ W] in
private theorem scaledProjection_apply (t : ℝ) (x : E × W) :
    scaledProjection t x = t • x.2 := rfl

/-- Multiply a fixed-support test by the standard bump at `t` times its transverse coordinate. -/
def normalCutoffTest (t : ℝ) {K : Compacts (E × W)} (f : 𝓓_{K}(E × W, ℝ)) :
    𝓓_{K}(E × W, ℝ) where
  toFun x := (transverseBump (W := W)) (scaledProjection t x) * f x
  contDiff' := by
    let L : E × W →L[ℝ] W := scaledProjection t
    exact ((transverseBump (W := W)).contDiff.comp L.contDiff).mul f.contDiff
  zero_on_compl' x hx := by
    change (transverseBump (W := W)) (scaledProjection t x) * f x = 0
    rw [show f x = 0 from f.zero_on_compl hx, mul_zero]

private theorem norm_iteratedFDeriv_le_supSeminorm {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {K : Compacts X}
    (f : 𝓓_{K}(X, ℝ)) {i m : ℕ} (hi : i ≤ m) (x : X) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ ContDiffMapSupportedIn.supSeminorm ℝ X ℝ ⊤ K m f :=
  (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
    ((Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℝ X ℝ ⊤ K)
      (Finset.mem_Iic.mpr hi)) f)

private theorem exists_supSeminorm_normalCutoffTest_bound {K : Compacts (E × W)}
    (f : 𝓓_{K}(E × W, ℝ)) (m : ℕ)
    (hflat : ∀ x : E, ∀ i ≤ m, iteratedFDeriv ℝ i f (x, 0) = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 1 ≤ t →
      ContDiffMapSupportedIn.supSeminorm ℝ (E × W) ℝ ⊤ K m (normalCutoffTest t f) ≤ D * t⁻¹ := by
  let B : Compacts W := ⟨Metric.closedBall 0 1, isCompact_closedBall _ _⟩
  let χ : 𝓓_{B}(W, ℝ) := ContDiffMapSupportedIn.of_support_subset transverseBump.contDiff (by
    rw [transverseBump.support_eq]
    exact Metric.ball_subset_closedBall)
  let M := ContDiffMapSupportedIn.supSeminorm ℝ (E × W) ℝ ⊤ K (m + 1) f
  let C := ContDiffMapSupportedIn.supSeminorm ℝ W ℝ ⊤ B m χ
  let D := ∑ j ∈ Finset.Iic m, ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C * M)
  have hM : 0 ≤ M := apply_nonneg _ _
  have hC : 0 ≤ C := apply_nonneg _ _
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, fun t ht => ?_⟩
  have ht' : 0 < t := zero_lt_one.trans_le ht
  let L : E × W →L[ℝ] W := scaledProjection t
  have hL : ‖L‖ ≤ t := by
    change ‖t • ContinuousLinearMap.snd ℝ E W‖ ≤ t
    rw [norm_smul, Real.norm_of_nonneg ht'.le]
    exact mul_le_of_le_one_right ht'.le (ContinuousLinearMap.norm_snd_le _ _ _)
  have hC' (i : ℕ) (hi : i ≤ m) (x : E × W) :
      ‖iteratedFDeriv ℝ i (χ ∘ L) x‖ ≤ C * t ^ i := by
    rw [L.iteratedFDeriv_comp_right χ.contDiff x (WithTop.coe_le_coe.mpr le_top)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i χ (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ i χ (L x)‖ * ‖L‖ ^ i := by simp
      _ ≤ C * t ^ i := by
        gcongr
        exact norm_iteratedFDeriv_le_supSeminorm χ hi (L x)
  change ((Finset.Iic m).sup (ContDiffMapSupportedIn.seminorm ℝ (E × W) ℝ ⊤ K))
    (normalCutoffTest t f) ≤ D * t⁻¹
  apply Seminorm.finset_sup_apply_le (mul_nonneg hD (inv_nonneg.mpr ht'.le))
  intro j hj
  have hjm : j ≤ m := Finset.mem_Iic.mp hj
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ
    (mul_nonneg hD (inv_nonneg.mpr ht'.le)) j _).mpr
  intro x _
  change ‖iteratedFDeriv ℝ j (fun y => (χ ∘ L) y * f y) x‖ ≤ D * t⁻¹
  refine (norm_iteratedFDeriv_mul_le (χ.contDiff.comp L.contDiff) f.contDiff x
    (WithTop.coe_le_coe.mpr le_top)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * (C * M)) * t⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hB : L x ∈ (B : Set W)
      · have hdist : ‖x.2‖ ≤ t⁻¹ := by
          have hb : ‖t • x.2‖ ≤ 1 := by
            simpa only [B, L, scaledProjection_apply, Compacts.coe_mk, Metric.mem_closedBall,
              dist_zero_right] using hB
          rw [norm_smul, Real.norm_of_nonneg ht'.le] at hb
          rw [← one_div, le_div_iff₀ ht', mul_comm]
          exact hb
        have hf' : ‖iteratedFDeriv ℝ (j - i) f x‖ ≤ M * (t⁻¹) ^ (i + 1) := by
          have hh := norm_iteratedFDeriv_le_pow_of_flat f.contDiff (x.1, 0) m hM
            (hflat x.1) (fun l hl y => norm_iteratedFDeriv_le_supSeminorm f hl y)
            (i + 1) (j - i) (by omega) x
          have hx : ‖x - (x.1, 0)‖ = ‖x.2‖ := by simp [Prod.norm_def]
          rw [hx] at hh
          exact hh.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hdist _) hM)
        calc
          _ ≤ (j.choose i : ℝ) * (C * t ^ i) * (M * (t⁻¹) ^ (i + 1)) := by
            gcongr
            exact hC' i (hij.trans hjm) x
          _ = ((j.choose i : ℝ) * (C * M)) * (t ^ i * (t⁻¹) ^ i) * t⁻¹ := by
            rw [pow_succ]
            ring
          _ = _ := by rw [← mul_pow, mul_inv_cancel₀ ht'.ne', one_pow, mul_one]
      · have hz : iteratedFDeriv ℝ i (χ ∘ L) x = 0 := by
          rw [L.iteratedFDeriv_comp_right χ.contDiff x (WithTop.coe_le_coe.mpr le_top)]
          rw [show iteratedFDeriv ℝ i χ (L x) = 0 from χ.iteratedFDeriv_zero_on_compl hB]
          ext v
          rfl
        rw [hz, norm_zero, mul_zero, zero_mul]
        positivity
    _ ≤ D * t⁻¹ := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr ht'.le)
      exact Finset.single_le_sum
        (f := fun j : ℕ => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C * M))
        (fun j _ => by positivity) hj

/-- A distribution vanishing away from a coordinate subspace kills any fixed-support
test whose derivatives through the compact order all vanish on that subspace. -/
theorem distribution_eq_zero_of_flatProductJet {Ω : Opens (E × W)} (T : 𝓓'(Ω, F))
    (hT : Distribution.IsVanishingOn T {x : E × W | x.2 ≠ 0})
    {K : Compacts (E × W)} (hK : (K : Set (E × W)) ⊆ Ω)
    (f : 𝓓_{K}(E × W, ℝ))
    (hflat : ∀ x : E, ∀ i ≤ smoothDistributionCompactOrder T hK,
      iteratedFDeriv ℝ i f (x, 0) = 0) :
    T (TestFunction.ofSupportedIn hK f) = 0 := by
  have heq (t : ℝ) :
      T (TestFunction.ofSupportedIn hK f) =
        T (TestFunction.ofSupportedIn hK (normalCutoffTest t f)) := by
    have hs : tsupport (TestFunction.ofSupportedIn hK (f - normalCutoffTest t f)) ⊆
        {x : E × W | x.2 ≠ 0} := by
      intro z hz hz₀
      have hL : scaledProjection t z = (0 : W) := by rw [scaledProjection_apply, hz₀, smul_zero]
      have hlim : Tendsto (scaledProjection t : E × W →L[ℝ] W) (𝓝 z) (𝓝 0) :=
        hL ▸ (scaledProjection t).continuous.continuousAt
      have he : ∀ᶠ x in 𝓝 z, (transverseBump (W := W)) (scaledProjection t x) = 1 :=
        hlim.eventually (transverseBump (W := W)).eventuallyEq_one
      have hz' : (TestFunction.ofSupportedIn hK (f - normalCutoffTest t f) : E × W → ℝ)
          =ᶠ[𝓝 z] 0 := by
        filter_upwards [he] with x hx
        change f x - (transverseBump (W := W)) (scaledProjection t x) * f x = 0
        rw [hx, one_mul, sub_self]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hz') hz
    have h := hT (TestFunction.ofSupportedIn hK (f - normalCutoffTest t f)) hs
    change T (TestFunction.ofSupportedInCLM ℝ hK (f - normalCutoffTest t f)) = 0 at h
    rwa [map_sub, map_sub, sub_eq_zero] at h
  obtain ⟨C, _, hC⟩ := exists_bound_smoothDistributionCompactOrder T hK
  obtain ⟨D, _, hD⟩ := exists_supSeminorm_normalCutoffTest_bound f _ hflat
  have he : ∀ᶠ t : ℝ in atTop, ‖T (TestFunction.ofSupportedIn hK f)‖ ≤ (C : ℝ) * D * t⁻¹ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [heq t, mul_assoc]
    exact (hC _).trans (mul_le_mul_of_nonneg_left (hD t ht) C.coe_nonneg)
  have hlim : Tendsto (fun t : ℝ => (C : ℝ) * D * t⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).const_mul ((C : ℝ) * D)
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim he) (norm_nonneg _))

omit [FiniteDimensional ℝ W] in
/-- Vanishing of the transverse jets along the whole coordinate subspace
implies vanishing of the full jets of the same orders there. -/
theorem iteratedFDeriv_eq_zero_of_transverseJets {f : E × W → F} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (h : ∀ x : E, ∀ i ≤ m, ∀ v : Fin i → W,
      iteratedFDeriv ℝ i f (x, 0) (fun k => (0, v k)) = 0)
    (i : ℕ) (hi : i ≤ m) (x : E) : iteratedFDeriv ℝ i f (x, 0) = 0 := by
  induction i generalizing x with
  | zero =>
      ext v
      have he : v = fun k => ((0 : E), (0 : Fin 0 → W) k) := Subsingleton.elim _ _
      rw [he]
      exact h x 0 hi 0
  | succ i ih =>
      let g := iteratedFDeriv ℝ i f
      let L := ContinuousLinearMap.inl ℝ E W
      have hg : g ∘ L = 0 := funext fun y => ih (Nat.le_of_succ_le hi) y
      have hd : Differentiable ℝ g :=
        hf.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top i))
      have he := ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
      rw [hg, fderiv_zero] at he
      let M := iteratedFDeriv ℝ (i + 1) f (x, 0)
      have htan (v : Fin (i + 1) → E × W) (hv : (v 0).2 = 0) : M v = 0 := by
        have hl : L (v 0).1 = v 0 := Prod.ext rfl hv.symm
        have hz := congrArg (fun A : E →L[ℝ] (E × W) [×i]→L[ℝ] F => A (v 0).1) he.symm
        change fderiv ℝ g (x, 0) (L (v 0).1) = 0 at hz
        change iteratedFDeriv ℝ (i + 1) f (x, 0) v = 0
        rw [iteratedFDeriv_succ_apply_left, ← hl, hz, zero_apply]
      have hslot (v : Fin (i + 1) → E × W) (j : Fin (i + 1)) (hv : (v j).2 = 0) :
          M v = 0 := by
        have hp := Langlands.Analysis.iteratedFDeriv_comp_perm_of_contDiffAt (𝕜 := ℝ)
          (hf.contDiffAt (x := (x, 0))) (WithTop.coe_le_coe.mpr le_top) v (Equiv.swap 0 j)
        change M (v ∘ Equiv.swap 0 j) = M v at hp
        rw [← hp]
        exact htan _ (by simpa using hv)
      ext v
      let vT : Fin (i + 1) → E × W := fun k => ((v k).1, 0)
      let vN : Fin (i + 1) → E × W := fun k => (0, (v k).2)
      have hv : v = vT + vN := funext fun k => by
        exact Prod.ext (by simp [vT, vN]) (by simp [vT, vN])
      change M v = 0
      rw [hv]
      change M.toMultilinearMap (vT + vN) = 0
      rw [M.toMultilinearMap.map_add_univ]
      apply Finset.sum_eq_zero
      intro s _
      by_cases hs : s = ∅
      · subst s
        rw [Finset.piecewise_empty]
        exact h x (i + 1) hi (fun k => (v k).2)
      · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        exact hslot (s.piecewise vT vN) j (by simp [Finset.piecewise, hj, vT])

/-- A supported distribution on a product depends on a finite transverse jet
on each fixed compact-support step. -/
theorem distribution_eq_zero_of_transverseProductJet {Ω : Opens (E × W)} (T : 𝓓'(Ω, F))
    (hT : Distribution.IsVanishingOn T {x : E × W | x.2 ≠ 0})
    {K : Compacts (E × W)} (hK : (K : Set (E × W)) ⊆ Ω)
    (f : 𝓓_{K}(E × W, ℝ))
    (hflat : ∀ x : E, ∀ i ≤ smoothDistributionCompactOrder T hK, ∀ v : Fin i → W,
      iteratedFDeriv ℝ i f (x, 0) (fun k => (0, v k)) = 0) :
    T (TestFunction.ofSupportedIn hK f) = 0 :=
  distribution_eq_zero_of_flatProductJet T hT hK f
    (fun x i hi => iteratedFDeriv_eq_zero_of_transverseJets f.contDiff _ hflat i hi x)

end Langlands.HarmonicAnalysis
