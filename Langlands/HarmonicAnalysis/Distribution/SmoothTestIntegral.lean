import Langlands.HarmonicAnalysis.Distribution.SmoothTestParameters
import Langlands.Analysis.CompactWeightedIntegral

/-! # Compact parameter integrals of smooth tests -/

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Classical ContDiff Distributions BoundedContinuousFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

universe u v

variable {P : Type u} {E : Type v}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private abbrev compactIntegralCLM {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℂ) →L[ℂ] ℂ :=
  Langlands.Analysis.compactWeightedIntegral μ (1 : C(X, ℂ))

private theorem compactIntegralCLM_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    compactIntegralCLM μ f = ∫ x, f x ∂μ := by
  simp [compactIntegralCLM, smul_eq_mul]

/-- Integration over a compact parameter set preserves the smooth fixed-support tests and
commutes with every continuous linear functional on that test space. -/
def SmoothTestIntegralStatement : Prop :=
  ∀ {P : Type u} {E : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : Compacts P) (K : Compacts E)
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    (h : P × E → ℂ) (hh : ContDiff ℝ ∞ h) (hs : ∀ t ∈ Q, ∀ x ∉ K, h (t, x) = 0),
    ∃ f : 𝓓_{K}(E, ℂ), (∀ x, f x = ∫ t : Q, h (t.val, x) ∂μ) ∧
      ∀ L : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ, L f = ∫ t : Q, L (compactTestFamily hh hs t) ∂μ

set_option maxHeartbeats 1200000 in
theorem smoothTestIntegral : SmoothTestIntegralStatement.{u, v} := by
  intro P E _ _ _ _ Q K _ _ μ _ h hh hs
  let : CompactSpace Q := isCompact_iff_compactSpace.mp Q.isCompact
  let A (x : E) : C(Q, ℂ) := ⟨fun t => h (t.val, x),
    hh.continuous.comp (continuous_subtype_val.prodMk continuous_const)⟩
  have hA : ContDiff ℝ ∞ A := by
    apply contDiffOn_univ.mp
    exact Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint (f := A)
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Q, P)) isOpen_univ isOpen_univ (fun _ => mem_univ _)
      ((hh.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn) (fun _ _ _ => rfl)
  let I := (compactIntegralCLM μ).restrictScalars ℝ
  let f : 𝓓_{K}(E, ℂ) :=
    ⟨I ∘ A, I.contDiff.comp hA, fun x hx => by
      change compactIntegralCLM μ (A x) = 0
      rw [compactIntegralCLM_apply]
      simp only [A, ContinuousMap.coe_mk, fun t : Q => hs t.val t.property x hx, integral_zero]⟩
  refine ⟨f, fun x => compactIntegralCLM_apply μ (A x), ?_⟩
  intro L
  let family : Q → 𝓓_{K}(E, ℂ) := compactTestFamily hh hs
  have hFamily : Continuous family := continuous_compactTestFamily hh hs
  let p := ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K
  let q := (normSeminorm ℂ ℂ).comp L.toLinearMap
  obtain ⟨s, C, _, hBound⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℂ E ℂ ⊤ K) q (continuous_norm.comp L.continuous)
  let V := (i : ↥s) → (E →ᵇ (E [×i.val]→L[ℝ] ℂ))
  let : NormedAddCommGroup V := inferInstanceAs (NormedAddCommGroup ((i : ↥s) →
    (E →ᵇ (E [×i.val]→L[ℝ] ℂ))))
  let : NormedSpace ℝ V := inferInstanceAs (NormedSpace ℝ ((i : ↥s) →
    (E →ᵇ (E [×i.val]→L[ℝ] ℂ))))
  let : NormedSpace ℂ V := inferInstanceAs (NormedSpace ℂ ((i : ↥s) →
    (E →ᵇ (E [×i.val]→L[ℝ] ℂ))))
  let : CompleteSpace V := inferInstanceAs (CompleteSpace ((i : ↥s) →
    (E →ᵇ (E [×i.val]→L[ℝ] ℂ))))
  let J : 𝓓_{K}(E, ℂ) →L[ℂ] V := ContinuousLinearMap.pi fun i =>
    ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ i.val
  have hJNorm : s.sup p ≤ (normSeminorm ℂ V).comp J.toLinearMap := by
    apply Finset.sup_le
    intro i hi F
    change ‖J F ⟨i, hi⟩‖ ≤ ‖J F‖
    exact norm_le_pi_norm (J F) (⟨i, hi⟩ : ↥s)
  have hControl (F : 𝓓_{K}(E, ℂ)) : ‖L F‖ ≤ (C : ℝ) * ‖J F‖ :=
    (hBound F).trans (mul_le_mul_of_nonneg_left (hJNorm F) C.coe_nonneg)
  have hJetInt : Integrable (fun t => J (family t)) μ :=
    (J.continuous.comp hFamily).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJet : (∫ t, J (family t) ∂μ) = J f := by
    funext i
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    let pi : V →L[ℝ] (E →ᵇ (E [×i.val]→L[ℝ] ℂ)) := ContinuousLinearMap.proj i
    let d : V →L[ℝ] ℂ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i.val => E) ℂ v).comp
      ((BoundedContinuousFunction.evalCLM ℝ x).comp pi)
    change d (∫ t, J (family t) ∂μ) = d (J f)
    rw [← d.integral_comp_comm hJetInt]
    change (∫ t, ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ i.val (family t) x v ∂μ) =
      ContDiffMapSupportedIn.structureMapCLM ℂ ⊤ i.val f x v
    simp only [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    have hSlice (t : Q) : ((family t : 𝓓_{K}(E, ℂ)) : E → ℂ) =
        (ContinuousMap.evalCLM ℝ t) ∘ A := rfl
    simp only [hSlice, ContinuousLinearMap.iteratedFDeriv_comp_left _ hA.contDiffAt (by simp)]
    change (∫ t, iteratedFDeriv ℝ i.val A x v t ∂μ) = iteratedFDeriv ℝ i.val (I ∘ A) x v
    rw [I.iteratedFDeriv_comp_left hA.contDiffAt (by simp)]
    exact (compactIntegralCLM_apply μ (iteratedFDeriv ℝ i.val A x v)).symm
  let D := J.prod L
  let S := (LinearMap.range D.toLinearMap).topologicalClosure
  have hClosed : IsClosed (S : Set (V × ℂ)) := Submodule.isClosed_topologicalClosure _
  let : CompleteSpace S := hClosed.completeSpace_coe
  have hRange (F : 𝓓_{K}(E, ℂ)) : D F ∈ S :=
    Submodule.le_topologicalClosure _ ⟨F, rfl⟩
  let G (t : Q) : S := ⟨D (family t), hRange _⟩
  have hG : Integrable G μ := ((D.continuous.comp hFamily).subtype_mk _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  let y := ∫ t, D (family t) ∂μ
  have hy : y ∈ S := by
    change (∫ t, S.subtypeL (G t) ∂μ) ∈ S
    rw [S.subtypeL.integral_comp_comm hG]
    exact (∫ t, G t ∂μ).property
  have hyInt : Integrable (fun t => D (family t)) μ :=
    (D.continuous.comp hFamily).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hy1 : y.1 = J f := by
    change (ContinuousLinearMap.fst ℂ V ℂ) (∫ t, D (family t) ∂μ) = J f
    rw [← (ContinuousLinearMap.fst ℂ V ℂ).integral_comp_comm hyInt]
    exact hJet
  have hy2 : y.2 = ∫ t, L (family t) ∂μ := by
    change (ContinuousLinearMap.snd ℂ V ℂ) (∫ t, D (family t) ∂μ) = _
    rw [← (ContinuousLinearMap.snd ℂ V ℂ).integral_comp_comm hyInt]
    rfl
  have hClosure : (S : Set (V × ℂ)) ⊆ {p | ‖p.2‖ ≤ (C : ℝ) * ‖p.1‖} := by
    apply closure_minimal _ (isClosed_le continuous_snd.norm (continuous_const.mul continuous_fst.norm))
    rintro _ ⟨F, rfl⟩
    exact hControl F
  have h := hClosure (sub_mem hy (hRange f))
  change ‖y.2 - L f‖ ≤ (C : ℝ) * ‖y.1 - J f‖ at h
  rw [hy1, sub_self, norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero, hy2] at h
  exact h.symm

end Langlands.HarmonicAnalysis
