import Langlands.HarmonicAnalysis.Distribution.SmoothDistributionLocality

/-! # Local multipliers and derivatives of tests along smooth vector fields -/

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E}

private theorem exists_contDiff_eqOn_of_isCompact [FiniteDimensional ℝ E]
    {χ : E → ℝ} (hχ : ContDiffOn ℝ ∞ χ Ω) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ EqOn η χ K := by
  obtain ⟨s, hs, hKs, hsΩ⟩ := normal_exists_closure_subset hK.isClosed Ω.isOpen hKΩ
  obtain ⟨b, hb, _, hbs, hbK⟩ := exists_contDiff_support_eq_eq_one_iff hs hK.isClosed hKs
    (n := (⊤ : ℕ∞))
  refine ⟨fun x => b x * χ x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Ω
    · exact hb.contDiffAt.mul (hχ.contDiffAt (Ω.isOpen.mem_nhds hx))
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      have hxo : x ∈ (closure s)ᶜ := fun h => hx (hsΩ h)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxo] with y hy
      have hyb : y ∉ support b := fun h => hy (subset_closure (hbs ▸ h))
      change b y * χ y = 0
      rw [notMem_support.mp hyb, zero_mul]
  · intro x hx
    change b x * χ x = χ x
    rw [(hbK x).mp hx, one_mul]

/-- Multiplication of tests by a scalar function smooth on their open domain. -/
def localScalarMultiplierCLM [FiniteDimensional ℝ E]
    {χ : E → ℝ} (hχ : ContDiffOn ℝ ∞ χ Ω) : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) := by
  classical
  let h (K : Compacts E) (hK : (K : Set E) ⊆ Ω) :=
    exists_contDiff_eqOn_of_isCompact hχ K.isCompact hK
  let η (K : Compacts E) (hK : (K : Set E) ⊆ Ω) := (h K hK).choose
  have hη (K : Compacts E) (hK : (K : Set E) ⊆ Ω) :
      ContDiff ℝ ∞ (η K hK) ∧ EqOn (η K hK) χ K := (h K hK).choose_spec
  have hsmooth (f : 𝓓(Ω, ℝ)) : ContDiff ℝ ∞ (fun x => f x * χ x) := by
    let K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
    have heq : (fun x => f x * χ x) = fun x => f x * η K f.tsupport_subset x := by
      funext x
      by_cases hx : x ∈ tsupport f
      · rw [(hη K f.tsupport_subset).2 hx]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
    rw [heq]
    exact f.contDiff.mul (hη K f.tsupport_subset).1
  refine TestFunction.limitCLM ℝ
    (fun f => ⟨fun x => f x * χ x, hsmooth f, f.hasCompactSupport.mul_right,
      tsupport_mul_subset_left.trans f.tsupport_subset⟩)
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ hK).comp
      (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (hη K hK).1))
    (fun K hK f => ?_)
  ext x
  change f x * χ x = f x * η K hK x
  by_cases hx : x ∈ K
  · rw [(hη K hK).2 hx]
  · simp [f.zero_on_compl hx]

@[simp]
theorem localScalarMultiplierCLM_apply [FiniteDimensional ℝ E]
    {χ : E → ℝ} (hχ : ContDiffOn ℝ ∞ χ Ω) (f : 𝓓(Ω, ℝ)) (x : E) :
    localScalarMultiplierCLM hχ f x = f x * χ x := rfl

private theorem tsupport_fderiv_vectorField_subset (V : E → E) (f : 𝓓(Ω, F)) :
    tsupport (fun x => fderiv ℝ f x (V x)) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra h
  apply hx
  change fderiv ℝ f x (V x) = 0
  rw [fderiv_of_notMem_tsupport ℝ h, zero_apply]

/-- Differentiation of a test along a vector field smooth on the test domain. -/
def smoothVectorFieldDerivativeTest {V : E → E} (hV : ContDiffOn ℝ ∞ V Ω)
    (f : 𝓓(Ω, F)) : 𝓓(Ω, F) := by
  have hs := tsupport_fderiv_vectorField_subset V f
  refine ⟨fun x => fderiv ℝ f x (V x), contDiff_iff_contDiffAt.mpr ?_,
    f.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans f.tsupport_subset⟩
  intro x
  by_cases hx : x ∈ Ω
  · exact (f.contDiff.fderiv_right (by simp)).contDiffAt.clm_apply
      (hV.contDiffAt (Ω.isOpen.mem_nhds hx))
  · have hx' : x ∈ (tsupport f)ᶜ := fun h => hx (f.tsupport_subset h)
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx'] with y hy
    rw [fderiv_of_notMem_tsupport ℝ hy, zero_apply]

@[simp]
theorem smoothVectorFieldDerivativeTest_apply {V : E → E} (hV : ContDiffOn ℝ ∞ V Ω)
    (f : 𝓓(Ω, F)) (x : E) :
    smoothVectorFieldDerivativeTest hV f x = fderiv ℝ f x (V x) := rfl

theorem tsupport_smoothVectorFieldDerivativeTest_subset {V : E → E}
    (hV : ContDiffOn ℝ ∞ V Ω) (f : 𝓓(Ω, F)) :
    tsupport (smoothVectorFieldDerivativeTest hV f) ⊆ tsupport f :=
  tsupport_fderiv_vectorField_subset V f

/-- A weighted sum of vector fields annihilated by a distribution gives a
derivative identity with the correction obtained by differentiating the weights. -/
theorem eval_smoothVectorFieldDerivativeTest_add_multiplier_eq_zero
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (T : 𝓓'(Ω, F))
    {V : ι → E → E} {β : ι → E → ℝ}
    (hV : ∀ j, ContDiffOn ℝ ∞ (V j) Ω) (hβ : ∀ j, ContDiffOn ℝ ∞ (β j) Ω)
    (hT : ∀ j (f : 𝓓(Ω, ℝ)), T (smoothVectorFieldDerivativeTest (hV j) f) = 0)
    {W : E → E} (hW : ContDiffOn ℝ ∞ W Ω)
    (hW_eq : ∀ x ∈ Ω, W x = ∑ j, β j x • V j x)
    {b : E → ℝ} (hb : ContDiffOn ℝ ∞ b Ω)
    (hb_eq : ∀ x ∈ Ω, b x = ∑ j, fderiv ℝ (β j) x (V j x))
    (f : 𝓓(Ω, ℝ)) :
    T (smoothVectorFieldDerivativeTest hW f + localScalarMultiplierCLM hb f) = 0 := by
  classical
  let g (j : ι) := smoothVectorFieldDerivativeTest (hV j) (localScalarMultiplierCLM (hβ j) f)
  have heq : ∑ j, g j =
      smoothVectorFieldDerivativeTest hW f + localScalarMultiplierCLM hb f := by
    ext x
    change (FunLike.coeAddMonoidHom 𝓓(Ω, ℝ) E ℝ (∑ j, g j)) x = _
    rw [map_sum, Finset.sum_apply]
    by_cases hx : x ∈ Ω
    · change (∑ j, (g j) x) = fderiv ℝ f x (W x) + f x * b x
      simp only [g, smoothVectorFieldDerivativeTest_apply]
      have hderiv (j : ι) :
          fderiv ℝ (localScalarMultiplierCLM (hβ j) f) x (V j x) =
            f x * fderiv ℝ (β j) x (V j x) + β j x * fderiv ℝ f x (V j x) := by
        have hf := (f.contDiff.differentiable (by simp) x).hasFDerivAt
        have hβ' := ((hβ j).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt
          (by simp)
        change fderiv ℝ ((f : E → ℝ) * β j) x (V j x) = _
        rw [(hf.mul hβ'.hasFDerivAt).fderiv]
        simp [smul_eq_mul]
      simp only [hderiv, hW_eq x hx, hb_eq x hx, map_sum, map_smul, smul_eq_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      exact add_comm _ _
    · change (∑ j, g j x) =
        (smoothVectorFieldDerivativeTest hW f + localScalarMultiplierCLM hb f) x
      rw [TestFunction.zero_on_compl _ hx]
      exact Finset.sum_eq_zero fun j _ => (g j).zero_on_compl hx
  rw [← heq, map_sum]
  exact Finset.sum_eq_zero fun j _ => hT j _

end Langlands.HarmonicAnalysis
