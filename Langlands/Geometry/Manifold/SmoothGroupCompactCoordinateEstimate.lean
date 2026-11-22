import Langlands.Geometry.Manifold.SmoothGroupDifferential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # An invariant derivative estimate in smooth coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Langlands.Geometry.Manifold

variable {E W G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [Group G] [TopologicalSpace G] [ChartedSpace W G] [LieGroup 𝓘(ℝ, W) ∞ G]

local notation "IE" => 𝓘(ℝ, E)
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "J" => Fin (Module.finrank ℝ W)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] in
private theorem continuous_coordinateOrbitDifferential (ψ : E → G)
    (hψ : ContMDiff IE IG ∞ ψ) :
    let D : G × E → E →L[ℝ] W :=
      fun p => mfderiv IE IG (fun y => p.1⁻¹ * (ψ p.2)⁻¹ * ψ y * p.1) p.2
    Continuous D := by
  let H (p : G × E) (y : E) := p.1⁻¹ * (ψ p.2)⁻¹ * ψ y * p.1
  have hH : ContMDiff (ModelWithCorners.prod (ModelWithCorners.prod IG IE) IE) IG ∞
      (Function.uncurry H) :=
    (((contMDiff_fst.comp contMDiff_fst).inv.mul
      (hψ.comp (contMDiff_snd.comp contMDiff_fst)).inv).mul
      (hψ.comp contMDiff_snd)).mul (contMDiff_fst.comp contMDiff_fst)
  have hH₁ (p : G × E) : H p p.2 = 1 := by simp [H]
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp := (hH (p, p.2)).mfderiv H Prod.snd
    (contMDiffAt_snd : ContMDiffAt (ModelWithCorners.prod IG IE) IE ∞ Prod.snd p)
    (m := ∞) (by simp)
  have heq :
      inTangentCoordinates IE IG Prod.snd (fun z => H z z.2)
        (fun z => mfderiv IE IG (H z) z.2) p =
          (fun q : G × E => show E →L[ℝ] W from mfderiv IE IG (H q) q.2) := by
    funext q
    rw [inTangentCoordinates_eq _ _ _ (by simp) (by simp [hH₁])]
    simp only [tangentBundleCore_coordChange_model_space, hH₁, ContinuousLinearMap.comp_id]
    let Lq : E →L[ℝ] W := mfderiv IE IG (H q) q.2
    change ((tangentBundleCore IG G).coordChange (achart W 1) (achart W 1) 1).comp Lq = Lq
    ext y
    exact (tangentBundleCore IG G).coordChange_self (achart W 1) 1 (mem_achart_source W 1) (Lq y)
  simpa only [heq] using hp.continuousAt

omit [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace W G]
  [LieGroup IG ∞ G] in
private theorem opNorm_le_of_basisValues_le (A : W →L[ℝ] ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j : J, ‖A (Module.finBasis ℝ W j)‖ ≤ M) :
    ‖A‖ ≤ (∑ j : J, ‖((Module.finBasis ℝ W).coord j).toContinuousLinearMap‖) * M := by
  let b := Module.finBasis ℝ W
  let c (j : J) := (b.coord j).toContinuousLinearMap
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hM)
  intro v
  calc
    ‖A v‖ = ‖∑ j, c j v • A (b j)‖ := by
      simpa only [map_sum, map_smul, c, LinearMap.coe_toContinuousLinearMap',
        Module.Basis.coord_apply] using congrArg (fun w => ‖A w‖) (b.sum_repr v).symm
    _ ≤ ∑ j, ‖c j v • A (b j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖c j‖ * ‖v‖) * M := Finset.sum_le_sum fun j _ => by
      rw [norm_smul]
      exact mul_le_mul (ContinuousLinearMap.le_opNorm _ _) (h j) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ j, ‖c j‖) * M * ‖v‖ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

/-- On a fixed compact coordinate ball and compact set of right factors, finitely many fixed
right-orbit derivatives bound the oscillation from the coordinate origin by a constant times
the coordinate distance. The constant is independent of the left factor and the function. -/
def SmoothGroupCompactCoordinateEstimateStatement (ψ : E → G) : Prop :=
  ContMDiff IE IG ∞ ψ →
  ∀ (K : Set G), IsCompact K → ∀ B : ℝ, 0 ≤ B →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ K, ∀ v ∈ closedBall (0 : E) B, ∀ x : G,
  ∀ f : G → ℂ, ContMDiff IG IC ∞ f → ∀ M : ℝ, 0 ≤ M →
  (∀ z ∈ closedBall (0 : E) B, ∀ j : J,
    ‖groupDirectionalValue IG (Module.finBasis ℝ W j) f (x * ψ z * k)‖ ≤ M) →
  ‖f (x * ψ v * k) - f (x * ψ 0 * k)‖ ≤ C * ‖v‖ * M

theorem smoothGroupCompactCoordinateEstimate (ψ : E → G) :
    SmoothGroupCompactCoordinateEstimateStatement (W := W) ψ := by
  intro hψ K hK B hB
  let b := Module.finBasis ℝ W
  let V := ∑ j : J, ‖(b.coord j).toContinuousLinearMap‖
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let L (p : G × E) : E →L[ℝ] W :=
    mfderiv IE IG (fun y => p.1⁻¹ * (ψ p.2)⁻¹ * ψ y * p.1) p.2
  have hL : Continuous L := continuous_coordinateOrbitDifferential ψ hψ
  let S := closedBall (0 : E) B
  obtain ⟨D, hD⟩ := ((hK.prod (isCompact_closedBall (0 : E) B)).image hL.norm).bddAbove
  let C := max 0 D
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C * V, mul_nonneg hC hV, fun k hk v hv x f hf M hM hbound => ?_⟩
  let F (y : E) : ℂ := f (x * ψ y * k)
  have hF : ContMDiff IE IC ∞ F :=
    hf.comp ((contMDiff_const.mul hψ).mul contMDiff_const)
  have hd (z : E) (hz : z ∈ S) : ‖fderiv ℝ F z‖ ≤ C * V * M := by
    let a (y : G) := f ((x * ψ z * k) * y)
    let p (y : E) := k⁻¹ * (ψ z)⁻¹ * ψ y * k
    let A : W →L[ℝ] ℂ := mvfderiv IG a 1
    have ha : ContMDiff IG IC ∞ a := hf.comp (contMDiff_const.mul contMDiff_id)
    have hp : ContMDiff IE IG ∞ p := (contMDiff_const.mul hψ).mul contMDiff_const
    have hp₁ : p z = 1 := by simp [p]
    have heq : F = a ∘ p := by funext y; dsimp [F, a, p]; group
    have hD' : fderiv ℝ F z = A.comp (L (k, z)) := by
      rw [heq, ← mvfderiv_eq_fderiv,
        mvfderiv_comp z (ha.mdifferentiableAt (by simp)) (hp.mdifferentiableAt (by simp))]
      change (mvfderiv IG a (p z) : W →L[ℝ] ℂ).comp (L (k, z)) = _
      rw [hp₁]
    have haB : ‖A‖ ≤ V * M :=
      opNorm_le_of_basisValues_le _ hM (hbound z hz)
    have hLB : ‖L (k, z)‖ ≤ C :=
      (hD ⟨(k, z), ⟨hk, hz⟩, rfl⟩).trans (le_max_right _ _)
    calc
      ‖fderiv ℝ F z‖ ≤ ‖A‖ * ‖L (k, z)‖ := by
        rw [hD']
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (V * M) * C := mul_le_mul haB hLB (norm_nonneg _) (mul_nonneg hV hM)
      _ = C * V * M := by ring
  have h₀ : (0 : E) ∈ S := mem_closedBall_self hB
  have h := (convex_closedBall (0 : E) B).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hF.contDiff.differentiable (by simp)).differentiableAt (x := z)) hd h₀ hv
  rw [sub_zero, mul_right_comm (C * V) M ‖v‖] at h
  exact h

end Langlands.Geometry.Manifold
