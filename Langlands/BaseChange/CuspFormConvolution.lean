import Langlands.BaseChange.CuspFormConvolutionStatement

/-!
# Cusp forms form a two-sided ideal of the Hecke algebra of `GL_n(F)`

Proof of `Langlands.BaseChange.CuspFormConvolutionStatement`: for a nonarchimedean local field
`F`, a Haar measure `μ` on `GL_n(F)` and test functions `f g`, the convolution
`Hecke.TestFunction.convolution μ f g` has vanishing constant terms as soon as `f` or `g` has.
The argument is a compact-support Fubini computation on `U × G`, proved first for an arbitrary
topological group `G` with a closed subgroup `U`. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Function Set Topology
open scoped Pointwise

namespace Langlands.BaseChange

universe u v

open HarmonicAnalysis (SchwartzBruhat)

section General

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {U : Subgroup G}

omit [MeasurableSpace G] [BorelSpace G] in
/-- For a closed subgroup `U`, the map `u ↦ x * u * y` is a closed embedding of `U` into `G`. -/
theorem isClosedEmbedding_mul_coe_mul (hU : IsClosed (U : Set G)) (x y : G) :
    IsClosedEmbedding (fun u : U => x * (u : G) * y) :=
  ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight y)).isClosedEmbedding.comp
    hU.isClosedEmbedding_subtypeVal

/-- A two-sided translate of a test function, restricted to a closed subgroup, is continuous with
compact support, hence integrable for every measure that is finite on compact sets. -/
theorem integrable_comp_mul_coe_mul (hU : IsClosed (U : Set G)) (ν : Measure U)
    [IsFiniteMeasureOnCompacts ν] (φ : SchwartzBruhat G) (x y : G) :
    Integrable (fun u : U => φ (x * (u : G) * y)) ν :=
  (φ.continuous.comp ((continuous_const.mul continuous_subtype_val).mul
      continuous_const)).integrable_of_hasCompactSupport
    (φ.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbedding_mul_coe_mul hU x y))

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- **Right ideal.** If `g` is cuspidal along a closed subgroup `U`, so is `f * g`:
`∫_U (f * g)(x u y) dν(u) = ∫_G f(z) ∫_U g(z⁻¹ x u y) dν(u) dμ(z) = 0`. -/
theorem integral_convolution_eq_zero_of_right (hU : IsClosed (U : Set G)) (ν : Measure U)
    [IsFiniteMeasureOnCompacts ν] (f g : SchwartzBruhat G)
    (hg : HarishChandraSchwartz.IsUnipotentCuspidal ν (g : G → ℂ)) (x y : G) :
    ∫ u : U, Hecke.TestFunction.convolution μ f g (x * (u : G) * y) ∂ν = 0 := by
  simp only [Hecke.TestFunction.convolution_apply]
  rw [integral_integral_swap_of_hasCompactSupport
    (f := fun (u : U) (z : G) => f z * g (z⁻¹ * (x * (u : G) * y)))]
  · have h0 : ∀ z : G, ∫ u : U, f z * g (z⁻¹ * (x * (u : G) * y)) ∂ν = 0 := by
      intro z
      rw [integral_const_mul]
      have h := hg (z⁻¹ * x) y
      simp only [mul_assoc] at h ⊢
      rw [h, mul_zero]
    simp only [h0, integral_zero]
  · exact (f.continuous.comp continuous_snd).mul (g.continuous.comp
      (continuous_snd.inv.mul ((continuous_const.mul
        (continuous_subtype_val.comp continuous_fst)).mul continuous_const)))
  · have hK : IsCompact
        (((fun u : U => x * (u : G) * y) ⁻¹' (support (f : G → ℂ) * support (g : G → ℂ))) ×ˢ
          support (f : G → ℂ)) :=
      ((isClosedEmbedding_mul_coe_mul hU x y).isCompact_preimage
        ((Hecke.TestFunction.isCompact_support f).mul
          (Hecke.TestFunction.isCompact_support g))).prod
        (Hecke.TestFunction.isCompact_support f)
    refine HasCompactSupport.of_support_subset_isCompact hK ?_
    rintro ⟨u, z⟩ hp
    change f z * g (z⁻¹ * (x * (u : G) * y)) ≠ 0 at hp
    have h := mul_ne_zero_iff.mp hp
    exact ⟨⟨z, h.1, z⁻¹ * (x * (u : G) * y), h.2, by simp⟩, h.1⟩

variable [μ.IsMulLeftInvariant]

omit [IsFiniteMeasureOnCompacts μ] in
/-- Left invariance of `μ`: `(f * g)(a y) = ∫_G f(a w) g(w⁻¹ y) dμ(w)`. -/
theorem convolution_apply_mul_eq (f g : SchwartzBruhat G) (a y : G) :
    Hecke.TestFunction.convolution μ f g (a * y) = ∫ w, f (a * w) * g (w⁻¹ * y) ∂μ := by
  rw [Hecke.TestFunction.convolution_apply,
    ← integral_mul_left_eq_self (fun z => f z * g (z⁻¹ * (a * y))) a]
  congr 1
  funext w
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- **Left ideal.** If `f` is cuspidal along a closed subgroup `U`, so is `f * g`:
`∫_U (f * g)(x u y) dν(u) = ∫_G (∫_U f(x u w) dν(u)) g(w⁻¹ y) dμ(w) = 0`. -/
theorem integral_convolution_eq_zero_of_left (hU : IsClosed (U : Set G)) (ν : Measure U)
    [IsFiniteMeasureOnCompacts ν] (f g : SchwartzBruhat G)
    (hf : HarishChandraSchwartz.IsUnipotentCuspidal ν (f : G → ℂ)) (x y : G) :
    ∫ u : U, Hecke.TestFunction.convolution μ f g (x * (u : G) * y) ∂ν = 0 := by
  simp only [convolution_apply_mul_eq]
  rw [integral_integral_swap_of_hasCompactSupport
    (f := fun (u : U) (w : G) => f (x * (u : G) * w) * g (w⁻¹ * y))]
  · have h0 : ∀ w : G, ∫ u : U, f (x * (u : G) * w) * g (w⁻¹ * y) ∂ν = 0 := by
      intro w
      rw [integral_mul_const, hf x w, zero_mul]
    simp only [h0, integral_zero]
  · exact (f.continuous.comp ((continuous_const.mul
        (continuous_subtype_val.comp continuous_fst)).mul continuous_snd)).mul
      (g.continuous.comp (continuous_snd.inv.mul continuous_const))
  · set L : Set G := (fun w : G => w⁻¹ * y) ⁻¹' support (g : G → ℂ) with hL
    have hLc : IsCompact L := by
      have := (Hecke.TestFunction.isCompact_support g).image
        (show Continuous (fun k : G => y * k⁻¹) from continuous_const.mul continuous_inv)
      convert this using 1
      ext w
      simp only [hL, mem_preimage, mem_image]
      constructor
      · intro hw
        exact ⟨w⁻¹ * y, hw, by group⟩
      · rintro ⟨k, hk, rfl⟩
        simpa using hk
    have hK : IsCompact
        (((fun u : U => x * (u : G) * 1) ⁻¹' (support (f : G → ℂ) * L⁻¹)) ×ˢ L) :=
      ((isClosedEmbedding_mul_coe_mul hU x 1).isCompact_preimage
        ((Hecke.TestFunction.isCompact_support f).mul hLc.inv)).prod hLc
    refine HasCompactSupport.of_support_subset_isCompact hK ?_
    rintro ⟨u, w⟩ hp
    change f (x * (u : G) * w) * g (w⁻¹ * y) ≠ 0 at hp
    have h := mul_ne_zero_iff.mp hp
    refine ⟨⟨x * (u : G) * w, h.1, w⁻¹, by simpa [hL] using h.2, by simp⟩, h.2⟩

end General

/-- **Cusp forms form a two-sided ideal of the Hecke algebra of `GL_n(F)`.** -/
theorem cuspFormConvolution : CuspFormConvolutionStatement.{u} := by
  intro F _ _ _ _ n μ _ f g
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  have : T2Space F := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    let := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  refine ⟨fun hg => ?_, fun hf => ?_⟩
  · intro B hB ν hν
    have hU := B.isClosed_unipotentSubgroup F
    obtain ⟨-, hgc⟩ := hg B hB ν hν
    exact ⟨fun x y => integrable_comp_mul_coe_mul hU ν _ x y,
      fun x y => integral_convolution_eq_zero_of_right μ hU ν f g hgc x y⟩
  · intro B hB ν hν
    have hU := B.isClosed_unipotentSubgroup F
    obtain ⟨-, hfc⟩ := hf B hB ν hν
    exact ⟨fun x y => integrable_comp_mul_coe_mul hU ν _ x y,
      fun x y => integral_convolution_eq_zero_of_left μ hU ν f g hfc x y⟩

end Langlands.BaseChange
