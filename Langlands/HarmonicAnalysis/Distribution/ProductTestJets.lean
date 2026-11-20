import Langlands.Analysis.SmoothIteratedFDerivSymm
import Langlands.HarmonicAnalysis.Distribution.ProductTestKernel

/-! # Transverse derivatives of smooth tests on a product -/

noncomputable section

open Set Topology TopologicalSpace WithSeminorms
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The iterated Fréchet derivative as a continuous linear map on smooth tests. -/
def iteratedFDerivTestCLM {U : Opens E} (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] : (i : ℕ) → 𝓓(U, F) →L[ℝ] 𝓓(U, E [×i]→L[ℝ] F)
  | 0 => TestFunction.postcompCLM (Ω := U) (n := ⊤)
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  | i + 1 =>
    let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm
    let D := TestFunction.fderivCLM (Ω := U) (F := E [×i]→L[ℝ] F) ℝ ⊤ ⊤
    (TestFunction.postcompCLM (Ω := U) (n := ⊤) e.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (D.comp (iteratedFDerivTestCLM F i))

@[simp]
theorem iteratedFDerivTestCLM_apply {U : Opens E} (i : ℕ) (f : 𝓓(U, F)) :
    ⇑(iteratedFDerivTestCLM F i f) = iteratedFDeriv ℝ i f := by
  induction i with
  | zero =>
    simp only [iteratedFDerivTestCLM, TestFunction.postcompCLM_apply,
      iteratedFDeriv_zero_eq_comp, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  | succ i ih =>
    have h : (⊤ : ℕ∞) + 1 ≤ ⊤ := le_top
    simp only [iteratedFDerivTestCLM, ContinuousLinearMap.comp_apply,
      TestFunction.postcompCLM_apply, TestFunction.fderivCLM_apply_of_le _ h,
      ih, iteratedFDeriv_succ_eq_comp_left, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]

private theorem isClosedEmbedding_zeroSection :
    IsClosedEmbedding (ContinuousLinearMap.inl ℝ E W) := by
  refine ⟨isEmbedding_prodMkLeft (0 : W), ?_⟩
  have hrange : range (ContinuousLinearMap.inl ℝ E W) = {z : E × W | z.2 = 0} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro hz
      exact ⟨z.1, Prod.ext rfl hz.symm⟩
  rw [hrange]
  exact isClosed_eq continuous_snd continuous_const

private def zeroSectionSupport (K : Compacts (E × W)) : Compacts E :=
  ⟨ContinuousLinearMap.inl ℝ E W ⁻¹' (K : Set (E × W)),
    isClosedEmbedding_zeroSection.isCompact_preimage K.isCompact⟩

private theorem zeroSectionSupport_subset {U : Opens E} {V : Opens W}
    {K : Compacts (E × W)} (hK : (K : Set (E × W)) ⊆ productTestDomain U V) :
    (zeroSectionSupport K : Set E) ⊆ U :=
  fun _ hx => (mem_productTestDomain.mp (hK hx)).1

private def zeroSectionCompactTest {K : Compacts (E × W)} (f : 𝓓_{K}(E × W, F)) :
    𝓓_{zeroSectionSupport K}(E, F) :=
  ContDiffMapSupportedIn.of_support_subset
    (f.contDiff.comp (ContinuousLinearMap.inl ℝ E W).contDiff)
    (fun _ hx => f.support_subset hx)

private def zeroSectionCompactTestCLM (K : Compacts (E × W)) :
    𝓓_{K}(E × W, F) →L[ℝ] 𝓓_{zeroSectionSupport K}(E, F) := by
  let L : 𝓓_{K}(E × W, F) →ₗ[ℝ] 𝓓_{zeroSectionSupport K}(E, F) :=
    { toFun := zeroSectionCompactTest
      map_add' := by intro f g; ext x; rfl
      map_smul' := by intro c f; ext x; rfl }
  refine ⟨L, continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (ContDiffMapSupportedIn.withSeminorms ..) L (Seminorm.IsBounded.of_real fun i => ?_)⟩
  refine ⟨{i}, 1, fun f => ?_⟩
  simp only [Finset.sup_singleton, one_mul]
  refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (apply_nonneg _ _) i _).mpr ?_
  intro x _
  let ι := ContinuousLinearMap.inl ℝ E W
  change ‖iteratedFDeriv ℝ i (f ∘ ι) x‖ ≤
    ContDiffMapSupportedIn.seminorm ℝ (E × W) F ⊤ K i f
  rw [ι.iteratedFDeriv_comp_right f.contDiff x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) ?_).trans
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ))
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ E W)

private def zeroSectionTest {U : Opens E} {V : Opens W}
    (f : 𝓓(productTestDomain U V, F)) : 𝓓(U, F) :=
  let K : Compacts (E × W) := ⟨tsupport f, f.hasCompactSupport⟩
  TestFunction.ofSupportedIn (zeroSectionSupport_subset (K := K) f.tsupport_subset)
    (zeroSectionCompactTest
      (ContDiffMapSupportedIn.of_support_subset f.contDiff (subset_tsupport (⇑f))))

/-- Restrict a smooth test on a product to the zero section of its second factor. -/
def productZeroSectionTestCLM {U : Opens E} {V : Opens W} :
    𝓓(productTestDomain U V, F) →L[ℝ] 𝓓(U, F) :=
  TestFunction.limitCLM ℝ zeroSectionTest
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ (zeroSectionSupport_subset hK)).comp
      (zeroSectionCompactTestCLM K))
    (fun _ _ _ => rfl)

@[simp]
theorem productZeroSectionTestCLM_apply {U : Opens E} {V : Opens W}
    (f : 𝓓(productTestDomain U V, F)) (x : E) :
    productZeroSectionTestCLM f x = f (x, 0) := rfl

/-- The order-`i` transverse derivative along the zero section, as a test on the first factor. -/
def transverseProductJetCLM {U : Opens E} {V : Opens W} (i : ℕ) :
    𝓓(productTestDomain U V, F) →L[ℝ] 𝓓(U, W [×i]→L[ℝ] F) :=
  (TestFunction.postcompCLM
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin i => ContinuousLinearMap.inr ℝ E W))).comp
    (productZeroSectionTestCLM.comp (iteratedFDerivTestCLM F i))

@[simp]
theorem transverseProductJetCLM_apply {U : Opens E} {V : Opens W} (i : ℕ)
    (f : 𝓓(productTestDomain U V, F)) (x : E) (v : Fin i → W) :
    transverseProductJetCLM i f x v = iteratedFDeriv ℝ i f (x, 0) (fun k => (0, v k)) := by
  simp only [transverseProductJetCLM, ContinuousLinearMap.comp_apply,
    TestFunction.postcompCLM_apply, Function.comp_apply, productZeroSectionTestCLM_apply,
    iteratedFDerivTestCLM_apply]
  rfl

/-- The transverse derivative is symmetric in its normal directions. -/
theorem transverseProductJetCLM_comp_perm {U : Opens E} {V : Opens W} (i : ℕ)
    (f : 𝓓(productTestDomain U V, F)) (x : E) (v : Fin i → W)
    (σ : Equiv.Perm (Fin i)) :
    transverseProductJetCLM i f x (v ∘ σ) = transverseProductJetCLM i f x v := by
  simp only [transverseProductJetCLM_apply]
  exact Langlands.Analysis.iteratedFDeriv_comp_perm_of_contDiffAt f.contDiff.contDiffAt
    (by simp) (fun k => (0, v k)) σ

end Langlands.HarmonicAnalysis
