import Langlands.Automorphic.CuspidalAdmissible.ExpPointwise
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential neighbourhoods of the identity in the adelic group

`expInf Zm` is `exp Zm` as an element of the infinite adelic group. The sets
`expBox δ L = {ofInfinite (exp Zm) · ofFinite l : ‖Zm‖ ≤ δ, l ∈ L}` are compact for compact `L`,
and neighbourhoods of the identity for `δ > 0` and a neighbourhood `L` of the identity
(inverse function theorem for `exp` at `0`).
-/

noncomputable section

universe u

open MeasureTheory NumberField Filter
open scoped Classical Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

open ArchimedeanGL

/-- `exp Zm` in the infinite adelic group. -/
def expInf (Zm : ArchimedeanMatrix K n) : InfiniteAdelicGL K n :=
  infiniteOneParameter K n ((realLieAlgebraToMatrix K n).symm Zm) 1

theorem archimedeanGLCoordinates_expInf_val (Zm : ArchimedeanMatrix K n) :
    ((archimedeanGLCoordinates K n (expInf K n Zm) : ArchimedeanGL K n) :
      ArchimedeanMatrix K n) = NormedSpace.exp Zm := by
  rw [expInf, infiniteOneParameter, ContinuousMulEquiv.apply_symm_apply, oneParameter_val,
    LinearEquiv.apply_symm_apply, one_smul]

theorem continuous_expInf : Continuous (expInf K n) := by
  refine (archimedeanGLCoordinates K n).symm.continuous.comp ?_
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun Zm : ArchimedeanMatrix K n => NormedSpace.exp
      ((1 : ℝ) • realLieAlgebraToMatrix K n ((realLieAlgebraToMatrix K n).symm Zm))
    simp only [LinearEquiv.apply_symm_apply, one_smul]
    exact NormedSpace.exp_continuous
  · change Continuous fun Zm : ArchimedeanMatrix K n => NormedSpace.exp
      (-((1 : ℝ) • realLieAlgebraToMatrix K n ((realLieAlgebraToMatrix K n).symm Zm)))
    simp only [LinearEquiv.apply_symm_apply, one_smul]
    exact NormedSpace.exp_continuous.comp continuous_neg

/-- The box `{ofInfinite (exp Zm) · ofFinite l : ‖Zm‖ ≤ δ, l ∈ L}`. -/
def expBox (δ : ℝ) (L : Set (FiniteAdelicGL K n)) : Set (AdelicGL K n) :=
  (fun p : ArchimedeanMatrix K n × FiniteAdelicGL K n =>
    AdelicGL.ofInfinite K n (expInf K n p.1) * AdelicGL.ofFinite K n p.2) ''
      (Metric.closedBall (0 : ArchimedeanMatrix K n) δ ×ˢ L)

theorem continuous_expBoxMap : Continuous (fun p : ArchimedeanMatrix K n × FiniteAdelicGL K n =>
    AdelicGL.ofInfinite K n (expInf K n p.1) * AdelicGL.ofFinite K n p.2) :=
  ((map_continuous (AdelicGL.ofInfinite K n)).comp ((continuous_expInf K n).comp continuous_fst)).mul
    ((map_continuous (AdelicGL.ofFinite K n)).comp continuous_snd)

theorem isCompact_expBox (δ : ℝ) {L : Set (FiniteAdelicGL K n)} (hL : IsCompact L) :
    IsCompact (expBox K n δ L) :=
  ((isCompact_closedBall (0 : ArchimedeanMatrix K n) δ).prod hL).image (continuous_expBoxMap K n)

/-- **Exponential boxes are neighbourhoods of the identity.** -/
theorem expBox_mem_nhds {δ : ℝ} (hδ : 0 < δ) {L : Set (FiniteAdelicGL K n)}
    (hL : L ∈ 𝓝 (1 : FiniteAdelicGL K n)) : expBox K n δ L ∈ 𝓝 (1 : AdelicGL K n) := by
  -- the inverse function theorem for `exp` at `0`
  have hmap : map NormedSpace.exp (𝓝 (0 : ArchimedeanMatrix K n)) =
      𝓝 (NormedSpace.exp (0 : ArchimedeanMatrix K n)) :=
    (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ArchimedeanMatrix K n)).map_nhds_eq_of_surj
      (LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩)
  rw [NormedSpace.exp_zero] at hmap
  have hE : NormedSpace.exp '' Metric.ball (0 : ArchimedeanMatrix K n) δ ∈
      𝓝 (1 : ArchimedeanMatrix K n) := by
    rw [← hmap]
    exact image_mem_map (Metric.ball_mem_nhds 0 hδ)
  have hE' : (fun u : AdelicGL K n => ((archimedeanGLCoordinates K n (AdelicGL.infinite K n u) :
      ArchimedeanGL K n) : ArchimedeanMatrix K n)) ⁻¹'
      (NormedSpace.exp '' Metric.ball (0 : ArchimedeanMatrix K n) δ) ∈ 𝓝 (1 : AdelicGL K n) := by
    refine ContinuousAt.preimage_mem_nhds ?_ ?_
    · exact (Units.continuous_val.comp ((archimedeanGLCoordinates K n).continuous.comp
        (map_continuous (AdelicGL.infinite K n)))).continuousAt
    · simpa using hE
  have hL' : (AdelicGL.finite K n) ⁻¹' L ∈ 𝓝 (1 : AdelicGL K n) :=
    (map_continuous (AdelicGL.finite K n)).continuousAt.preimage_mem_nhds (by simpa using hL)
  refine Filter.mem_of_superset (Filter.inter_mem hE' hL') ?_
  rintro u ⟨⟨Zm, hZm, hZu⟩, hu⟩
  refine ⟨(Zm, AdelicGL.finite K n u), ⟨Metric.ball_subset_closedBall hZm, hu⟩, ?_⟩
  have hinf : expInf K n Zm = AdelicGL.infinite K n u := by
    apply (archimedeanGLCoordinates K n).injective
    apply Units.ext
    rw [archimedeanGLCoordinates_expInf_val]
    exact hZu
  simp only
  rw [hinf]
  exact (AdelicGL.eq_ofInfinite_mul_ofFinite K n u).symm

end Langlands.Global
