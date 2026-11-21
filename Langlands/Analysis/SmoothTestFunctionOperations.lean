import Mathlib.Analysis.Distribution.TestFunction

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace Langlands.Analysis

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {Ω Ω' : Opens A}

private def fixedSupportPullback (e : A ≃L[ℝ] A) (K : Compacts A) :
    𝓓_{K}(A, ℂ) →L[ℂ] 𝓓_{K.map e.symm e.symm.continuous}(A, ℂ) := by
  refine ContDiffMapSupportedIn.mkCLM ℂ (fun f => f ∘ e) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun f => f.contDiff.comp e.contDiff) (fun f x hx => ?_) ?_
  · exact f.zero_on_compl (fun he => hx ⟨e x, he, e.symm_apply_apply x⟩)
  · intro i hi
    refine ⟨{i}, ‖e.toContinuousLinearMap‖ ^ i, by positivity, fun f x _ => ?_⟩
    change ‖iteratedFDeriv ℝ i (f ∘ e.toContinuousLinearMap) x‖ ≤ _
    rw [e.toContinuousLinearMap.iteratedFDeriv_comp_right f.contDiff x (mod_cast hi)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sup_singleton]
    rw [mul_comm (‖e.toContinuousLinearMap‖ ^ i)]
    exact mul_le_mul_of_nonneg_right
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
      (pow_nonneg (norm_nonneg _) _)

/-- Pullback of complex test functions by a real continuous linear equivalence. -/
def testLinearPullback (e : A ≃L[ℝ] A) (he : MapsTo e.symm Ω Ω') :
    𝓓(Ω, ℂ) →L[ℂ] 𝓓(Ω', ℂ) := by
  let p (f : 𝓓(Ω, ℂ)) : 𝓓(Ω', ℂ) :=
    ⟨f ∘ e, f.contDiff.comp e.contDiff, f.hasCompactSupport.comp_homeomorph e.toHomeomorph,
      (tsupport_comp_subset_preimage f e.continuous).trans fun x hx => by
        rw [← e.symm_apply_apply x]
        exact he (f.tsupport_subset hx)⟩
  let T (K : Compacts A) (hK : (K : Set A) ⊆ Ω) : 𝓓_{K}(A, ℂ) →L[ℂ] 𝓓(Ω', ℂ) :=
    (TestFunction.ofSupportedInCLM ℂ (K := K.map e.symm e.symm.continuous) (by
      rintro _ ⟨x, hx, rfl⟩
      exact he (hK hx))).comp (fixedSupportPullback e K)
  exact TestFunction.limitCLM ℂ p T (fun _ _ _ => TestFunction.ext fun _ => rfl)

@[simp] theorem testLinearPullback_apply (e : A ≃L[ℝ] A) (he : MapsTo e.symm Ω Ω')
    (f : 𝓓(Ω, ℂ)) (x : A) :
    testLinearPullback e he f x = f (e x) := rfl

variable (V : A → A) (hV : ContDiff ℝ ∞ V)

private theorem tsupport_fderiv_apply_field_subset (f : A → ℂ) :
    tsupport (fun x => fderiv ℝ f x (V x)) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) isClosed_closure
  apply tsupport_fderiv_subset ℝ
  apply subset_tsupport _
  intro hzero
  apply hx
  change fderiv ℝ f x (V x) = 0
  rw [hzero, zero_apply]

/-- Differentiation along a smooth real vector field as a continuous complex-linear
operator on test functions. -/
def testVectorFieldDerivative : 𝓓(Ω, ℂ) →L[ℂ] 𝓓(Ω, ℂ) := by
  let d (f : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) := by
    have hs := tsupport_fderiv_apply_field_subset V (f : A → ℂ)
    exact ⟨fun x => fderiv ℝ f x (V x),
      (f.contDiff.fderiv_right (by simp)).clm_apply hV,
      f.hasCompactSupport.of_isClosed_subset isClosed_closure hs, hs.trans f.tsupport_subset⟩
  let D : 𝓓(Ω, ℂ) →L[ℝ] 𝓓(Ω, ℂ) := TestFunction.limitCLM ℝ d
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ hK).comp
      ((ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.id ℝ (A →L[ℝ] ℂ)) hV).comp
        (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)))
    (fun K hK f => TestFunction.ext fun x => by
      change fderiv ℝ (f : A → ℂ) x (V x) =
        ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f x (V x)
      rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f (by simp)])
  exact
    { toFun := d
      map_add' := D.map_add
      map_smul' := fun c f => TestFunction.ext fun x => by
        change fderiv ℝ (c • (f : A → ℂ)) x (V x) = c • fderiv ℝ f x (V x)
        rw [fderiv_const_smul (f.contDiff.differentiable (by simp) x) c]
        rfl
      cont := D.continuous }

@[simp] theorem testVectorFieldDerivative_apply (f : 𝓓(Ω, ℂ)) (x : A) :
    testVectorFieldDerivative V hV f x = fderiv ℝ f x (V x) := rfl

theorem tsupport_testVectorFieldDerivative_subset (f : 𝓓(Ω, ℂ)) :
    tsupport (testVectorFieldDerivative V hV f : A → ℂ) ⊆ tsupport f :=
  tsupport_fderiv_apply_field_subset V _

end Langlands.Analysis
