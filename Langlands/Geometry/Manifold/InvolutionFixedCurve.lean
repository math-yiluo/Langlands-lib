import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Smooth curves of fixed points of a smooth involution

Let `θ` be a smooth involution of a boundaryless manifold modelled on a real Banach space `E`
(with the model `𝓘(ℝ, E)`), and let `p` be a fixed point. Every tangent vector `X` at `p` with
`dθ_p X = X` is the velocity at `0` of a smooth curve `c : ℝ → M` with `c 0 = p` and
`θ (c t) = c t` for all `t`.

The proof linearizes the involution in the chart at `p`: if `σ` is the involution in the chart
and `A = Dσ(y₀)`, then `h y = y₀ + ½ ((y - y₀) + A (σ y - y₀))` has derivative the identity at
`y₀` and satisfies `h ∘ σ = y₀ + A (h - y₀)`. By the inverse function theorem `h` is a local
diffeomorphism near `y₀`, so the preimage of the line `y₀ + t X` consists of fixed points.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

set_option autoImplicit false

namespace Langlands.Geometry.Manifold.InvolutionFixedCurve

/-- A bounded smooth reparametrization of the real line with velocity `1` at `0`. -/
def bumpParam (δ t : ℝ) : ℝ := t / (1 + (t / δ) ^ 2)

theorem bumpParam_denom_pos (δ t : ℝ) : 0 < 1 + (t / δ) ^ 2 := by positivity

theorem contDiff_bumpParam (δ : ℝ) : ContDiff ℝ ∞ (bumpParam δ) := by
  unfold bumpParam
  exact contDiff_id.div (contDiff_const.add ((contDiff_id.div_const δ).pow 2))
    (fun t => (bumpParam_denom_pos δ t).ne')

theorem bumpParam_zero (δ : ℝ) : bumpParam δ 0 = 0 := by
  simp [bumpParam]

theorem abs_bumpParam_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : |bumpParam δ t| ≤ δ / 2 := by
  unfold bumpParam
  have hd := bumpParam_denom_pos δ t
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have h1 : (t / δ) ^ 2 = t ^ 2 / δ ^ 2 := by rw [div_pow]
  rw [h1]
  have key : |t| * δ * 2 ≤ δ ^ 2 + t ^ 2 := by
    have h2 := sq_nonneg (|t| - δ)
    have h3 := sq_abs t
    nlinarith
  rw [show δ / 2 * (1 + t ^ 2 / δ ^ 2) = (δ ^ 2 + t ^ 2) / (2 * δ) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [key]

theorem hasDerivAt_bumpParam (δ : ℝ) : HasDerivAt (bumpParam δ) 1 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have h0 : HasDerivAt (fun t : ℝ => t / δ) (1 / δ) 0 := HasDerivAt.div_const (hasDerivAt_id 0) δ
  have h2 : HasDerivAt (fun t : ℝ => 1 + (t / δ) ^ 2)
      (↑(2 : ℕ) * (0 / δ) ^ (2 - 1) * (1 / δ)) 0 :=
    HasDerivAt.const_add 1 (HasDerivAt.fun_pow h0 2)
  have h3 := HasDerivAt.fun_div h1 h2 (bumpParam_denom_pos δ 0).ne'
  have e : bumpParam δ = fun t => t / (1 + (t / δ) ^ 2) := rfl
  rw [e]
  convert h3 using 1
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **Fixed curves of a smooth involution.** -/
theorem exists_contMDiff_curve_fixed
    (θ : M → M) (hθ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ θ) (hθθ : ∀ x, θ (θ x) = x)
    (p : M) (hp : θ p = p) (X : E)
    (hX : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) θ p X = X) :
    ∃ c : ℝ → M, ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ c ∧ c 0 = p ∧ (∀ t, θ (c t) = c t) ∧
      mfderiv 𝓘(ℝ) 𝓘(ℝ, E) c 0 (1 : ℝ) = X := by
  classical
  set ψ := extChartAt 𝓘(ℝ, E) p with hψ
  set y₀ : E := ψ p with hy₀
  let σ : E → E := fun y => ψ (θ (ψ.symm y))
  have hsrc : IsOpen ψ.source := isOpen_extChartAt_source p
  have htgt : IsOpen ψ.target := isOpen_extChartAt_target p
  have hcont_symm : ContinuousOn ψ.symm ψ.target := continuousOn_extChartAt_symm p
  have hpsrc : p ∈ ψ.source := mem_extChartAt_source p
  have hy₀tgt : y₀ ∈ ψ.target := mem_extChartAt_target p
  have hsymm_y₀ : ψ.symm y₀ = p := extChartAt_to_inv p
  -- the open set where `σ` is defined and smooth
  let U : Set M := ψ.source ∩ θ ⁻¹' ψ.source
  have hU : IsOpen U := hsrc.inter (hsrc.preimage hθ.continuous)
  have hpU : p ∈ U := ⟨hpsrc, by simpa [hp] using hpsrc⟩
  let T0 : Set E := ψ.target ∩ ψ.symm ⁻¹' U
  have hT0 : IsOpen T0 := hcont_symm.isOpen_inter_preimage htgt hU
  have hy₀T0 : y₀ ∈ T0 := ⟨hy₀tgt, by rw [Set.mem_preimage, hsymm_y₀]; exact hpU⟩
  have hT0eq : ψ '' U = T0 := ψ.image_eq_target_inter_inv_preimage inter_subset_left
  have hσ_smooth : ContDiffOn ℝ ∞ σ T0 := by
    have h := (contMDiffOn_iff_of_subset_source' (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (x := p)
      (y := p) (f := θ) (s := U) (n := ∞) inter_subset_left
      (fun x hx => hx.2)).mp hθ.contMDiffOn
    rw [hT0eq] at h
    exact h
  have hσ_y₀ : σ y₀ = y₀ := by
    change ψ (θ (ψ.symm y₀)) = y₀
    rw [hsymm_y₀, hp]
  have hσ_maps : MapsTo σ T0 ψ.target := fun y hy => ψ.map_source hy.2.2
  have hσ_cont : ContinuousOn σ T0 := hσ_smooth.continuousOn
  -- the open set where `σ ∘ σ = id`
  let T1 : Set E := T0 ∩ σ ⁻¹' T0
  have hT1 : IsOpen T1 := hσ_cont.isOpen_inter_preimage hT0 hT0
  have hy₀T1 : y₀ ∈ T1 := ⟨hy₀T0, by rw [Set.mem_preimage, hσ_y₀]; exact hy₀T0⟩
  have hσσ : ∀ y ∈ T1, σ (σ y) = y := by
    intro y hy
    change ψ (θ (ψ.symm (ψ (θ (ψ.symm y))))) = y
    rw [ψ.left_inv hy.1.2.2, hθθ, ψ.right_inv hy.1.1]
  -- the linear part
  have hσ_diff : ContDiffAt ℝ ∞ σ y₀ := hσ_smooth.contDiffAt (hT0.mem_nhds hy₀T0)
  set A : E →L[ℝ] E := fderiv ℝ σ y₀ with hA
  have hσ_strict : HasStrictFDerivAt σ A y₀ :=
    hσ_diff.hasStrictFDerivAt (by simp)
  have hAA : A.comp A = ContinuousLinearMap.id ℝ E := by
    have h1 : HasFDerivAt (σ ∘ σ) (A.comp A) y₀ := by
      have hg : HasFDerivAt σ A (σ y₀) := by
        rw [hσ_y₀]
        exact hσ_strict.hasFDerivAt
      exact hg.comp y₀ hσ_strict.hasFDerivAt
    have h2 : (σ ∘ σ) =ᶠ[𝓝 y₀] id := by
      filter_upwards [hT1.mem_nhds hy₀T1] with y hy
      exact hσσ y hy
    exact (h1.congr_of_eventuallyEq h2.symm).unique (hasFDerivAt_id y₀)
  have hAX : A X = X := by
    have hmd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) θ p :=
      hθ.contMDiffAt.mdifferentiableAt (by simp)
    have h := hmd.mfderiv_abuse
    have hw : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) p θ = σ := by
      simp only [writtenInExtChartAt, hp]
      rfl
    rw [h, hw, modelWithCornersSelf_coe, range_id, fderivWithin_univ] at hX
    exact hX
  -- the linearizing map
  let h : E → E := fun y => y₀ + (1 / 2 : ℝ) • ((y - y₀) + A (σ y - y₀))
  have hh_y₀ : h y₀ = y₀ := by simp [h, hσ_y₀]
  have hh_smooth : ContDiffOn ℝ ∞ h T0 := by
    apply contDiffOn_const.add
    apply ContDiffOn.const_smul
    exact (contDiffOn_id.sub contDiffOn_const).add
      (A.contDiff.comp_contDiffOn (hσ_smooth.sub contDiffOn_const))
  have hh_strict : HasStrictFDerivAt h
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) y₀ := by
    have h1 : HasStrictFDerivAt (fun y => (y - y₀) + A (σ y - y₀))
        (ContinuousLinearMap.id ℝ E + A.comp A) y₀ :=
      ((hasStrictFDerivAt_id y₀).sub_const y₀).add
        (A.hasStrictFDerivAt.comp y₀ (hσ_strict.sub_const y₀))
    have h2 := (h1.const_smul (1 / 2 : ℝ)).const_add y₀
    convert h2 using 1
    rw [hAA]
    ext v
    simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply,
      smul_apply, add_apply]
    rw [← two_smul ℝ v, smul_smul]
    norm_num
  have hAA' (v : E) : A (A v) = v := by
    simpa using congrArg (fun L : E →L[ℝ] E => L v) hAA
  have hhσ : ∀ y ∈ T1, h (σ y) = y₀ + A (h y - y₀) := by
    intro y hy
    change y₀ + (1 / 2 : ℝ) • ((σ y - y₀) + A (σ (σ y) - y₀)) =
      y₀ + A ((y₀ + (1 / 2 : ℝ) • ((y - y₀) + A (σ y - y₀))) - y₀)
    rw [hσσ y hy, add_sub_cancel_left, map_smul, map_add, hAA', add_comm (A (y - y₀))]
  -- invertibility of the derivative near `y₀`
  have hh_fderiv_cont : ContinuousOn (fderiv ℝ h) T0 :=
    hh_smooth.continuousOn_fderiv_of_isOpen hT0 (by simp)
  let T2 : Set E := T0 ∩ fderiv ℝ h ⁻¹' range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)
  have hT2 : IsOpen T2 :=
    hh_fderiv_cont.isOpen_inter_preimage hT0 ContinuousLinearEquiv.isOpen
  have hy₀T2 : y₀ ∈ T2 :=
    ⟨hy₀T0, ⟨ContinuousLinearEquiv.refl ℝ E, hh_strict.hasFDerivAt.fderiv.symm⟩⟩
  -- the local inverse
  let Φ := hh_strict.toOpenPartialHomeomorph h
  have hΦsrc : y₀ ∈ Φ.source := hh_strict.mem_toOpenPartialHomeomorph_source
  have hΦcoe : ∀ y, Φ y = h y := fun _ => rfl
  let W : Set E := Φ.source ∩ T1 ∩ T2 ∩ (T0 ∩ σ ⁻¹' Φ.source)
  have hW : IsOpen W := ((Φ.open_source.inter hT1).inter hT2).inter
    (hσ_cont.isOpen_inter_preimage hT0 Φ.open_source)
  have hy₀W : y₀ ∈ W :=
    ⟨⟨⟨hΦsrc, hy₀T1⟩, hy₀T2⟩, hy₀T0, by rw [mem_preimage, hσ_y₀]; exact hΦsrc⟩
  let N : Set E := Φ.target ∩ Φ.symm ⁻¹' W
  have hN : IsOpen N := Φ.isOpen_inter_preimage_symm hW
  have hΦy₀ : Φ y₀ = y₀ := hh_y₀
  have hy₀tgtΦ : y₀ ∈ Φ.target := by
    rw [← hΦy₀]
    exact Φ.map_source hΦsrc
  have hΦsymm_y₀ : Φ.symm y₀ = y₀ := by
    conv_lhs => rw [← hΦy₀]
    exact Φ.left_inv hΦsrc
  have hy₀N : y₀ ∈ N := ⟨hy₀tgtΦ, by rw [mem_preimage, hΦsymm_y₀]; exact hy₀W⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hN y₀ hy₀N
  -- the curve in the chart
  set δ : ℝ := ρ / (‖X‖ + 1) with hδdef
  have hδ : 0 < δ := by positivity
  let u : ℝ → E := fun t => y₀ + bumpParam δ t • X
  have hu_mem : ∀ t, u t ∈ N := by
    intro t
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [u, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hX0 : 0 ≤ ‖X‖ := norm_nonneg X
    calc |bumpParam δ t| * ‖X‖ ≤ δ / 2 * ‖X‖ := by
          gcongr
          exact abs_bumpParam_le hδ t
      _ < ρ := by
          rw [hδdef]
          rw [show ρ / (‖X‖ + 1) / 2 * ‖X‖ = ρ * (‖X‖ / (2 * (‖X‖ + 1))) by
            field_simp]
          have hlt : ‖X‖ / (2 * (‖X‖ + 1)) < 1 := by
            rw [div_lt_one (by positivity)]
            linarith
          nlinarith
  have hu_smooth : ContDiff ℝ ∞ u :=
    contDiff_const.add ((contDiff_bumpParam δ).smul contDiff_const)
  let γ : ℝ → E := fun t => Φ.symm (u t)
  have hγW : ∀ t, γ t ∈ W := fun t => (hu_mem t).2
  have hγ_smooth : ContDiff ℝ ∞ γ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    have hut := hu_mem t
    have hsymm_t : Φ.symm (u t) ∈ W := hut.2
    obtain ⟨e, he⟩ := hsymm_t.1.2.2
    have hdiff : ContDiffAt ℝ ∞ h (Φ.symm (u t)) :=
      hh_smooth.contDiffAt (hT0.mem_nhds hsymm_t.1.2.1)
    have hfd : HasFDerivAt h (e : E →L[ℝ] E) (Φ.symm (u t)) := by
      rw [he]
      exact (hdiff.differentiableAt (by simp)).hasFDerivAt
    have hsymm := Φ.contDiffAt_symm (f₀' := e) hut.1 hfd hdiff
    exact hsymm.comp t hu_smooth.contDiffAt
  have hγ0 : γ 0 = y₀ := by
    change Φ.symm (y₀ + bumpParam δ 0 • X) = y₀
    rw [bumpParam_zero, zero_smul, add_zero, hΦsymm_y₀]
  have hγ_deriv : HasDerivAt γ X 0 := by
    have hu' : HasDerivAt u X 0 := by
      have := ((hasDerivAt_bumpParam δ).smul_const X).const_add y₀
      rw [one_smul] at this
      exact this
    have hu0 : u 0 = y₀ := by simp [u, bumpParam_zero]
    have hsymm' : HasFDerivAt Φ.symm
        ((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E) (u 0) := by
      rw [hu0]
      apply Φ.hasFDerivAt_symm hy₀tgtΦ
      rw [hΦsymm_y₀]
      exact hh_strict.hasFDerivAt
    have h3 := hsymm'.comp_hasDerivAt 0 hu'
    exact h3
  -- the curve on the manifold
  refine ⟨ψ.symm ∘ γ, ?_, ?_, ?_, ?_⟩
  · exact (contMDiffOn_extChartAt_symm p).comp_contMDiff hγ_smooth.contMDiff
      (fun t => (hγW t).1.1.2.1.1)
  · simp only [Function.comp_apply, hγ0, hsymm_y₀]
  · intro t
    have hy : γ t ∈ W := hγW t
    have hyT1 : γ t ∈ T1 := hy.1.1.2
    have hyΦ : γ t ∈ Φ.source := hy.1.1.1
    have hσyΦ : σ (γ t) ∈ Φ.source := hy.2.2
    have hhy : h (γ t) = u t := Φ.right_inv (hu_mem t).1
    have hfix : σ (γ t) = γ t := by
      apply Φ.injOn hσyΦ hyΦ
      rw [hΦcoe, hΦcoe, hhσ _ hyT1, hhy]
      simp only [u, add_sub_cancel_left, map_smul, hAX]
    have h2 : ψ.symm (ψ (θ (ψ.symm (γ t)))) = ψ.symm (γ t) := congrArg ψ.symm hfix
    rw [ψ.left_inv hyT1.1.2.2] at h2
    exact h2
  · have hc0 : (ψ.symm ∘ γ) 0 = p := by simp only [Function.comp_apply, hγ0, hsymm_y₀]
    have hmd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (ψ.symm ∘ γ) 0 :=
      ((contMDiffOn_extChartAt_symm p).comp_contMDiff hγ_smooth.contMDiff
        (fun t => (hγW t).1.1.2.1.1)).contMDiffAt.mdifferentiableAt (by simp)
    rw [hmd.mfderiv_abuse]
    have hw : writtenInExtChartAt 𝓘(ℝ) 𝓘(ℝ, E) 0 (ψ.symm ∘ γ) = γ := by
      funext t
      simp only [writtenInExtChartAt, hc0, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
        PartialEquiv.refl_coe, Function.comp_apply, id_eq]
      exact ψ.right_inv (hγW t).1.1.2.1.1
    rw [hw, modelWithCornersSelf_coe, range_id, fderivWithin_univ]
    have hfd : fderiv ℝ γ 0 = ContinuousLinearMap.toSpanSingleton ℝ X :=
      hγ_deriv.hasFDerivAt.fderiv
    show (fderiv ℝ γ 0 : ℝ →L[ℝ] E) (1 : ℝ) = X
    rw [hfd]
    simp

end Langlands.Geometry.Manifold.InvolutionFixedCurve
