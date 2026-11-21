import Langlands.HarmonicAnalysis.Distribution.ZeroSectionFieldVanishing

/-! # Infinitesimal covariance for a smooth weighted sum of vector fields -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] {Ω : Opens E} {V : ι → E → E} {β : ι → E → ℝ}

/-- The scalar correction for a distribution evaluated on a weighted derivative. -/
def fieldWeightDerivative (V : ι → E → E) (β : ι → E → ℝ) (x : E) : ℝ :=
  ∑ j, fderiv ℝ (β j) x (V j x)

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_fieldWeightDerivative
    (hV : ∀ j, ContDiffOn ℝ ∞ (V j) Ω) (hβ : ∀ j, ContDiffOn ℝ ∞ (β j) Ω) :
    ContDiffOn ℝ ∞ (fieldWeightDerivative V β) Ω :=
  ContDiffOn.sum fun j _ => ((hβ j).fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply (hV j)

private theorem sum_weightedDerivativeTest
    (hV : ∀ j, ContDiffOn ℝ ∞ (V j) Ω) (hβ : ∀ j, ContDiffOn ℝ ∞ (β j) Ω)
    {W : E → E} (hW : ContDiffOn ℝ ∞ W Ω) (hW_eq : ∀ x ∈ Ω, W x = ∑ j, β j x • V j x)
    (f : 𝓓(Ω, ℝ)) :
    (∑ j, smoothVectorFieldDerivativeTest (hV j) (localScalarMultiplierCLM (hβ j) f)) =
      shiftedVectorFieldDerivativeTest hW (contDiffOn_fieldWeightDerivative hV hβ) f := by
  let g (j : ι) := smoothVectorFieldDerivativeTest (hV j) (localScalarMultiplierCLM (hβ j) f)
  ext x
  change (FunLike.coeAddMonoidHom 𝓓(Ω, ℝ) E ℝ (∑ j, g j)) x = _
  rw [map_sum, Finset.sum_apply]
  by_cases hx : x ∈ Ω
  · change (∑ j, g j x) = fderiv ℝ f x (W x) + f x * fieldWeightDerivative V β x
    have hderiv (j : ι) : g j x =
        f x * fderiv ℝ (β j) x (V j x) + β j x * fderiv ℝ f x (V j x) := by
      have hf := (f.contDiff.differentiable (by simp) x).hasFDerivAt
      have hβ' := ((hβ j).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
      change fderiv ℝ ((f : E → ℝ) * β j) x (V j x) = _
      rw [(hf.mul hβ'.hasFDerivAt).fderiv]
      simp [smul_eq_mul]
    simp only [hderiv, hW_eq x hx, fieldWeightDerivative, map_sum, map_smul, smul_eq_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
    exact add_comm _ _
  · rw [TestFunction.zero_on_compl _ hx]
    exact Finset.sum_eq_zero fun j _ => (g j).zero_on_compl hx

/-- Weighting infinitesimal covariance identities preserves the common
eigenvalue when the weighted real eigenvalue factors sum to one. -/
theorem eval_weightedVectorFieldDerivativeTest
    (hV : ∀ j, ContDiffOn ℝ ∞ (V j) Ω) (hβ : ∀ j, ContDiffOn ℝ ∞ (β j) Ω)
    {W : E → E} (hW : ContDiffOn ℝ ∞ W Ω) (hW_eq : ∀ x ∈ Ω, W x = ∑ j, β j x • V j x)
    (T : 𝓓'(Ω, ℂ)) (eigen : ℂ) (q : ι → ℝ)
    (hT : ∀ j (f : 𝓓(Ω, ℝ)),
      T (smoothVectorFieldDerivativeTest (hV j) f) = eigen * (q j • T f))
    (hq : ∀ x ∈ Ω, (∑ j, q j * β j x) = 1) (f : 𝓓(Ω, ℝ)) :
    T (shiftedVectorFieldDerivativeTest hW (contDiffOn_fieldWeightDerivative hV hβ) f) =
      eigen * T f := by
  let g (j : ι) := localScalarMultiplierCLM (hβ j) f
  have hg : (∑ j, q j • g j) = f := by
    ext x
    change (FunLike.coeAddMonoidHom 𝓓(Ω, ℝ) E ℝ (∑ j, q j • g j)) x = f x
    rw [map_sum, Finset.sum_apply]
    by_cases hx : x ∈ Ω
    · change (∑ j, q j * (f x * β j x)) = f x
      simp_rw [mul_left_comm (q _) (f x)]
      rw [← Finset.mul_sum, hq x hx, mul_one]
    · rw [f.zero_on_compl hx]
      exact Finset.sum_eq_zero fun j _ => (q j • g j).zero_on_compl hx
  rw [← sum_weightedDerivativeTest hV hβ hW hW_eq, map_sum]
  simp_rw [hT, ← map_smul T]
  rw [← Finset.mul_sum, ← map_sum, hg]

/-- The weighted trace differs from the trace with weights frozen by the
scalar correction. -/
theorem trace_fderiv_weightedVectorField
    (hV : ∀ j, ContDiffOn ℝ ∞ (V j) Ω) (hβ : ∀ j, ContDiffOn ℝ ∞ (β j) Ω)
    {W : E → E} (hW_eq : ∀ x ∈ Ω, W x = ∑ j, β j x • V j x)
    {x : E} (hx : x ∈ Ω) :
    LinearMap.trace ℝ E (fderiv ℝ W x).toLinearMap =
      LinearMap.trace ℝ E (fderiv ℝ (fun y => ∑ j, β j x • V j y) x).toLinearMap +
        fieldWeightDerivative V β x := by
  let B (j : ι) := (fderiv ℝ (β j) x).smulRight (V j x)
  let C (j : ι) := β j x • fderiv ℝ (V j) x
  have hdV (j : ι) : HasFDerivAt (V j) (fderiv ℝ (V j) x) x :=
    (((hV j).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdβ (j : ι) : HasFDerivAt (β j) (fderiv ℝ (β j) x) x :=
    (((hβ j).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hD (j : ι) : HasFDerivAt (fun y => β j y • V j y) (C j + B j) x :=
    (hdβ j).smul (hdV j)
  have hD₀ (j : ι) : HasFDerivAt (fun y => β j x • V j y) (C j) x := (hdV j).const_smul _
  have he : W =ᶠ[𝓝 x] fun y => ∑ j, β j y • V j y := by
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact hW_eq y hy
  have hW := (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hD j).congr_of_eventuallyEq he
  have hW₀ := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hD₀ j
  have hlin (L : ι → E →L[ℝ] E) : (∑ j, L j).toLinearMap = ∑ j, (L j).toLinearMap := by
    ext z
    simp
  rw [hW.fderiv, hW₀.fderiv, hlin, hlin, map_sum, map_sum]
  simp only [ContinuousLinearMap.toLinearMap_add, map_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact LinearMap.trace_smulRight _ _

end Langlands.HarmonicAnalysis
