import Langlands.Global.ArchimedeanNormalizedKernelStatement
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Normalized compact smooth kernels in identity neighborhoods: proof -/

noncomputable section
universe u
open MeasureTheory Set Topology
open scoped Classical Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Real matrix coordinates of the actual completion-based group. -/
def matrixCoordinates (g : InfiniteAdelicGL K n) : ArchimedeanMatrix K n :=
  ((archimedeanGLCoordinates K n g : ArchimedeanGL K n) : ArchimedeanMatrix K n)

omit [NumberField K] in
theorem matrixCoordinates_one : matrixCoordinates K n 1 = 1 := by
  simp [matrixCoordinates]

theorem isOpenEmbedding_matrixCoordinates : IsOpenEmbedding (matrixCoordinates K n) := by
  have h := Units.isOpenEmbedding_val.comp
    (archimedeanGLCoordinates K n).toHomeomorph.isOpenEmbedding
  exact h

/-- A real smooth function of the matrix coordinates gives an actual smooth function. -/
theorem ofReal_comp_matrixCoordinates_mem {b : ArchimedeanMatrix K n → ℝ}
    (hb : ContDiff ℝ ∞ b) :
    (fun g => ((b (matrixCoordinates K n g) : ℝ) : ℂ)) ∈ smoothFunctions K n := by
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ _
  have h : ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞
      (fun x : ArchimedeanGL K n => ((b (x : ArchimedeanMatrix K n) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hb).contMDiff.comp (Units.contMDiff_val (𝕜 := ℝ))
  simpa only [matrixCoordinates, ContinuousMulEquiv.apply_symm_apply] using! h

/-- The proof of the normalized compact-kernel statement. -/
theorem normalizedCompactKernel : NormalizedCompactKernelStatement K n := by
  intro _ _ μ _ U hU
  have hp := isOpenEmbedding_matrixCoordinates K n
  have hpU : matrixCoordinates K n '' U ∈ 𝓝 (1 : ArchimedeanMatrix K n) := by
    rw [← matrixCoordinates_one K n, ← hp.map_nhds_eq]
    exact Filter.image_mem_map hU
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hpU
  let φ : ContDiffBump (1 : ArchimedeanMatrix K n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set S := matrixCoordinates K n ⁻¹' Metric.closedBall 1 r
  have hSU : S ⊆ U := by
    intro g hg
    obtain ⟨u, hu, hpu⟩ := hrU hg
    rwa [← hp.injective hpu]
  have hScpt : IsCompact S :=
    hp.isInducing.isCompact_preimage' (isCompact_closedBall 1 r)
      (hrU.trans (image_subset_range _ _))
  have hSclosed : IsClosed S := Metric.isClosed_closedBall.preimage hp.continuous
  -- Every function vanishing off the support of the coordinate bump has closed support in `S`.
  have hsupp : ∀ {E : Type} [Zero E] (F : InfiniteAdelicGL K n → E),
      (∀ g, φ (matrixCoordinates K n g) = 0 → F g = 0) → tsupport F ⊆ S := by
    intro E _ F hF
    apply closure_minimal _ hSclosed
    intro g hg
    have hφ : matrixCoordinates K n g ∈ Function.support φ := fun h0 => hg (hF g h0)
    rw [φ.support_eq] at hφ
    exact Metric.ball_subset_closedBall hφ
  let b : InfiniteAdelicGL K n → ℝ := fun g => φ (matrixCoordinates K n g)
  have hb_cont : Continuous b := φ.continuous.comp hp.continuous
  have hb_cs : HasCompactSupport b :=
    hScpt.of_isClosed_subset isClosed_closure (hsupp b fun _ h => h)
  let b' : InfiniteAdelicGL K n → ℝ := fun g => b g⁻¹
  have hb'_cont : Continuous b' := hb_cont.comp continuous_inv
  have hb'_cs : HasCompactSupport b' :=
    hb_cs.comp_homeomorph (Homeomorph.inv (InfiniteAdelicGL K n))
  have hφ_one : φ 1 = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hr).le)
  have hb'_one : b' 1 ≠ 0 := by
    simp only [b', b, inv_one, matrixCoordinates_one, hφ_one]
    exact one_ne_zero
  have hI : 0 < ∫ g, b' g ∂μ :=
    hb'_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hb'_cs
      (fun g => φ.nonneg) hb'_one
  set c : ℝ := (∫ g, b' g ∂μ)⁻¹ with hc
  have hc_pos : 0 < c := inv_pos.mpr hI
  let f : SmoothFunctions K n :=
    ⟨fun g => ((c * φ (matrixCoordinates K n g) : ℝ) : ℂ),
      ofReal_comp_matrixCoordinates_mem K n (contDiff_const.mul φ.contDiff)⟩
  have hf_tsupp : tsupport f.val ⊆ S :=
    hsupp f.val fun g h0 => by simp only [f, h0, mul_zero, Complex.ofReal_zero]
  have hf_cs : HasCompactSupport f.val := hScpt.of_isClosed_subset isClosed_closure hf_tsupp
  refine ⟨⟨f, hf_cs⟩, hf_tsupp.trans hSU, ?_, ?_, ?_⟩
  · intro g
    simp only [f, Complex.ofReal_re, Complex.ofReal_im, and_true]
    exact mul_nonneg hc_pos.le φ.nonneg
  · simp only [f, Complex.ofReal_re, matrixCoordinates_one, hφ_one, mul_one]
    exact hc_pos
  · change (∫ g, ((c * b' g : ℝ) : ℂ) ∂μ) = 1
    rw [integral_complex_ofReal, integral_const_mul, hc, inv_mul_cancel₀ hI.ne']
    simp

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    NormalizedCompactKernelStatement K n :=
  @normalizedCompactKernel

end Langlands.Global.ArchimedeanGL
