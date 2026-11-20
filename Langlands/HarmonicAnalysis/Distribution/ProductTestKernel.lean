import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Continuous extension of tests by a fixed kernel on a second factor -/

noncomputable section

open Set TopologicalSpace WithSeminorms
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W A F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The product of two bundled open sets, viewed in the ambient product space. -/
def productTestDomain (U : Opens E) (V : Opens W) : Opens (E × W) :=
  ⟨(U : Set E) ×ˢ (V : Set W), U.isOpen.prod V.isOpen⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ W] in
@[simp]
theorem mem_productTestDomain {U : Opens E} {V : Opens W} {z : E × W} :
    z ∈ productTestDomain U V ↔ z.1 ∈ U ∧ z.2 ∈ V := Iff.rfl

private theorem norm_iteratedFDeriv_comp_contraction {X Y G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : X →L[ℝ] Y) (hL : ‖L‖ ≤ 1) {f : Y → G} (hf : ContDiff ℝ ∞ f)
    (i : ℕ) (x : X) : ‖iteratedFDeriv ℝ i (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)

/-- Evaluate a test on the first factor against a fixed operator-valued test on the second. -/
def productKernelCompactTest {K : Compacts E} {L : Compacts W}
    (ψ : 𝓓_{L}(W, A →L[ℝ] F)) (φ : 𝓓_{K}(E, A)) : 𝓓_{K ×ˢ L}(E × W, F) :=
  ContDiffMapSupportedIn.of_support_subset
    ((ψ.contDiff.comp contDiff_snd).clm_apply (φ.contDiff.comp contDiff_fst)) (by
      intro z hz
      change z.1 ∈ K ∧ z.2 ∈ L
      change ψ z.2 (φ z.1) ≠ 0 at hz
      constructor
      · by_contra h
        exact hz (by simp only [φ.zero_on_compl h, Pi.zero_apply, map_zero])
      · by_contra h
        exact hz (by simp only [ψ.zero_on_compl h, Pi.zero_apply, zero_apply]))

@[simp]
theorem productKernelCompactTest_apply {K : Compacts E} {L : Compacts W}
    (ψ : 𝓓_{L}(W, A →L[ℝ] F)) (φ : 𝓓_{K}(E, A)) (z : E × W) :
    productKernelCompactTest ψ φ z = ψ z.2 (φ z.1) := rfl

private theorem norm_iteratedFDeriv_le_supSeminorm {X G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {K : Compacts X}
    (φ : 𝓓_{K}(X, G)) {j i : ℕ} (hji : j ≤ i) (x : X) :
    ‖iteratedFDeriv ℝ j φ x‖ ≤ ContDiffMapSupportedIn.supSeminorm ℝ X G ⊤ K i φ :=
  (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
    (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hji))

private theorem seminorm_productKernelCompactTest {K : Compacts E} {L : Compacts W}
    (ψ : 𝓓_{L}(W, A →L[ℝ] F)) (φ : 𝓓_{K}(E, A)) (i : ℕ) :
    ContDiffMapSupportedIn.seminorm ℝ (E × W) F ⊤ (K ×ˢ L) i (productKernelCompactTest ψ φ) ≤
      ((∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) *
        ContDiffMapSupportedIn.supSeminorm ℝ W (A →L[ℝ] F) ⊤ L i ψ) *
      ContDiffMapSupportedIn.supSeminorm ℝ E A ⊤ K i φ := by
  let C := ContDiffMapSupportedIn.supSeminorm ℝ W (A →L[ℝ] F) ⊤ L i ψ
  let P := ContDiffMapSupportedIn.supSeminorm ℝ E A ⊤ K i φ
  have hC : 0 ≤ C := apply_nonneg _ _
  have hP : 0 ≤ P := apply_nonneg _ _
  have hC' : 0 ≤ (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) * C * P :=
    mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hC) hP
  refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hC' i _).mpr ?_
  intro z _
  let f : E × W → A →L[ℝ] F := ψ ∘ ContinuousLinearMap.snd ℝ E W
  let g : E × W → A := φ ∘ ContinuousLinearMap.fst ℝ E W
  have hf : ContDiff ℝ ∞ f := ψ.contDiff.comp (ContinuousLinearMap.snd ℝ E W).contDiff
  have hg : ContDiff ℝ ∞ g := φ.contDiff.comp (ContinuousLinearMap.fst ℝ E W).contDiff
  have hfun : ⇑(productKernelCompactTest ψ φ) = fun z => f z (g z) := rfl
  rw [hfun]
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f z‖ * ‖iteratedFDeriv ℝ (i - j) g z‖ :=
      norm_iteratedFDeriv_clm_apply hf hg z (by simp)
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * C * P := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hfj : ‖iteratedFDeriv ℝ j f z‖ ≤ ‖iteratedFDeriv ℝ j ψ z.2‖ :=
        norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.snd ℝ E W)
          (ContinuousLinearMap.norm_snd_le ℝ E W) ψ.contDiff j z
      have hgj : ‖iteratedFDeriv ℝ (i - j) g z‖ ≤ ‖iteratedFDeriv ℝ (i - j) φ z.1‖ :=
        norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.fst ℝ E W)
          (ContinuousLinearMap.norm_fst_le ℝ E W) φ.contDiff (i - j) z
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfj.trans (norm_iteratedFDeriv_le_supSeminorm ψ hj' z.2))
          (Nat.cast_nonneg _))
        (hgj.trans (norm_iteratedFDeriv_le_supSeminorm φ (Nat.sub_le _ _) z.1))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) * C * P := by
      simp only [Finset.sum_mul]

/-- Continuity of the kernel extension on a fixed compact support. -/
def productKernelCompactTestCLM {K : Compacts E} {L : Compacts W}
    (ψ : 𝓓_{L}(W, A →L[ℝ] F)) : 𝓓_{K}(E, A) →L[ℝ] 𝓓_{K ×ˢ L}(E × W, F) := by
  let S : 𝓓_{K}(E, A) →ₗ[ℝ] 𝓓_{K ×ˢ L}(E × W, F) :=
    { toFun := productKernelCompactTest ψ
      map_add' := by intro φ χ; ext z; simp
      map_smul' := by intro c φ; ext z; simp }
  refine ⟨S, continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (ContDiffMapSupportedIn.withSeminorms ..) S (Seminorm.IsBounded.of_real fun i => ?_)⟩
  exact ⟨Finset.Iic i, _, fun φ => seminorm_productKernelCompactTest ψ φ i⟩

@[simp]
theorem productKernelCompactTestCLM_apply {K : Compacts E} {L : Compacts W}
    (ψ : 𝓓_{L}(W, A →L[ℝ] F)) (φ : 𝓓_{K}(E, A)) (z : E × W) :
    productKernelCompactTestCLM ψ φ z = ψ z.2 (φ z.1) := rfl

private def productKernelTest {U : Opens E} {V : Opens W}
    (ψ : 𝓓(V, A →L[ℝ] F)) (φ : 𝓓(U, A)) : 𝓓(productTestDomain U V, F) :=
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport⟩
  let L : Compacts W := ⟨tsupport ψ, ψ.hasCompactSupport⟩
  TestFunction.ofSupportedIn (K := K ×ˢ L)
    (fun _ hz => ⟨φ.tsupport_subset hz.1, ψ.tsupport_subset hz.2⟩)
    (productKernelCompactTest
      (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport (⇑ψ)))
      (ContDiffMapSupportedIn.of_support_subset φ.contDiff (subset_tsupport (⇑φ))))

/-- The continuous linear extension from tests on `U` to tests on `U × V`
obtained by evaluating against a fixed operator-valued kernel on `V`. -/
def productKernelTestCLM {U : Opens E} {V : Opens W} (ψ : 𝓓(V, A →L[ℝ] F)) :
    𝓓(U, A) →L[ℝ] 𝓓(productTestDomain U V, F) :=
  TestFunction.limitCLM ℝ (productKernelTest ψ) (fun K hK =>
    let L : Compacts W := ⟨tsupport ψ, ψ.hasCompactSupport⟩
    (TestFunction.ofSupportedInCLM ℝ (Ω := productTestDomain U V) (K := K ×ˢ L)
      (fun _ hz => ⟨hK hz.1, ψ.tsupport_subset hz.2⟩)).comp
      (productKernelCompactTestCLM
        (ContDiffMapSupportedIn.of_support_subset ψ.contDiff (subset_tsupport (⇑ψ)))))
    (fun _ _ _ => rfl)

@[simp]
theorem productKernelTestCLM_apply {U : Opens E} {V : Opens W}
    (ψ : 𝓓(V, A →L[ℝ] F)) (φ : 𝓓(U, A)) (z : E × W) :
    productKernelTestCLM ψ φ z = ψ z.2 (φ z.1) := rfl

end Langlands.HarmonicAnalysis
