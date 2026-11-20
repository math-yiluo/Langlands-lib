import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-! # Smooth test pullback and distribution transport in open charts -/

noncomputable section

open Set Filter TopologicalSpace WithSeminorms
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  (e : OpenPartialHomeomorph E F)

/-- The source of an open chart as a bundled open set. -/
abbrev chartSource : Opens E := ⟨e.source, e.open_source⟩

/-- The target of an open chart as a bundled open set. -/
abbrev chartTarget : Opens F := ⟨e.target, e.open_target⟩

local notation "U" => chartSource e
local notation "V" => chartTarget e

private def pullbackChartSupport (K : Compacts F) (hK : (K : Set F) ⊆ e.target) : Compacts E :=
  ⟨e.symm '' (K : Set F), K.isCompact.image_of_continuousOn (e.continuousOn_symm.mono hK)⟩

private theorem pullbackChartSupport_subset (K : Compacts F) (hK : (K : Set F) ⊆ e.target) :
    (pullbackChartSupport e K hK : Set E) ⊆ e.source := by
  rintro _ ⟨y, hy, rfl⟩
  exact e.map_target (hK hy)

open Classical in
private def pullbackChartFun (f : F → ℝ) (x : E) : ℝ :=
  if x ∈ e.source then f (e x) else 0

private theorem pullbackChartFun_eqOn (f : F → ℝ) : EqOn (pullbackChartFun e f) (f ∘ e) e.source := by
  intro x hx
  simp [pullbackChartFun, hx]

private theorem support_pullbackChartFun_subset {f : F → ℝ}
    (K : Compacts F) (hK : (K : Set F) ⊆ e.target) (hf : Function.support f ⊆ K) :
    Function.support (pullbackChartFun e f) ⊆ pullbackChartSupport e K hK := by
  intro x hx
  have hxU : x ∈ e.source := by
    by_contra h
    exact hx (by simp [pullbackChartFun, h])
  have hxK : e x ∈ (K : Set F) := hf (fun h => hx (by simp [pullbackChartFun, hxU, h]))
  exact ⟨e x, hxK, e.left_inv hxU⟩

variable [NormedSpace ℝ E] [NormedSpace ℝ F] (he : ContDiffOn ℝ ∞ e e.source)

include he in
private theorem contDiff_pullbackChartFun {f : F → ℝ} (hdf : ContDiff ℝ ∞ f)
    (K : Compacts F) (hK : (K : Set F) ⊆ e.target) (hf : Function.support f ⊆ K) :
    ContDiff ℝ ∞ (pullbackChartFun e f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hxU : x ∈ e.source
  · have ho := e.open_source.mem_nhds hxU
    apply (hdf.contDiffAt.comp x (he.contDiffAt ho)).congr_of_eventuallyEq
    filter_upwards [ho] with y hy
    exact pullbackChartFun_eqOn e f hy
  · have hxK : x ∉ (pullbackChartSupport e K hK : Set E) :=
      fun h => hxU (pullbackChartSupport_subset e K hK h)
    have hc := (pullbackChartSupport e K hK).isCompact.isClosed
    have hzero : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) x := contDiffAt_const
    apply hzero.congr_of_eventuallyEq
    filter_upwards [hc.isOpen_compl.mem_nhds hxK] with y hy
    exact Function.notMem_support.mp fun h => hy (support_pullbackChartFun_subset e K hK hf h)

private def pullbackChartCompactTest (K : Compacts F) (hK : (K : Set F) ⊆ e.target)
    (φ : 𝓓_{K}(F, ℝ)) : 𝓓_{pullbackChartSupport e K hK}(E, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_pullbackChartFun e he φ.contDiff K hK φ.support_subset)
    (support_pullbackChartFun_subset e K hK φ.support_subset)

include he in
private theorem exists_bound_chartDerivatives {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ e.source) (i : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ K, ∀ j : ℕ, 1 ≤ j → j ≤ i →
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B ^ j := by
  let P : E → ℝ := fun x => (Finset.range (i + 1)).sup' Finset.nonempty_range_add_one
    (fun j => ‖iteratedFDerivWithin ℝ j e e.source x‖)
  have hP : ContinuousOn P e.source := by
    apply ContinuousOn.finset_sup'_apply
    intro j _
    exact (he.continuousOn_iteratedFDerivWithin (by simp) e.open_source.uniqueDiffOn).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hP.mono hKU)
  let B := max (1 : ℝ) C
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, hB, fun x hx j hj hji => ?_⟩
  calc
    ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ P x :=
      Finset.le_sup' (fun l : ℕ => ‖iteratedFDerivWithin ℝ l e e.source x‖)
        (Finset.mem_range_succ_iff.mpr hji)
    _ ≤ ‖P x‖ := Real.le_norm_self _
    _ ≤ C := hC x hx
    _ ≤ B := le_max_right _ _
    _ ≤ B ^ j := by simpa only [pow_one] using pow_le_pow_right₀ hB hj

private theorem exists_bound_pullbackChartCompactTest (K : Compacts F)
    (hK : (K : Set F) ⊆ e.target) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓓_{K}(F, ℝ), ∀ x ∈ (pullbackChartSupport e K hK : Set E),
      ‖iteratedFDeriv ℝ i (pullbackChartCompactTest e he K hK φ) x‖ ≤
        C * ((Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm ℝ F ℝ ⊤ K)) φ := by
  let J := pullbackChartSupport e K hK
  obtain ⟨B, hB, hj⟩ := exists_bound_chartDerivatives e he J.isCompact
    (pullbackChartSupport_subset e K hK) i
  refine ⟨(i.factorial : ℝ) * B ^ i, by positivity, ?_⟩
  intro φ x hx
  have hxU := pullbackChartSupport_subset e K hK hx
  let ψ := pullbackChartCompactTest e he K hK φ
  change ‖iteratedFDeriv ℝ i ψ x‖ ≤ _
  have heq : iteratedFDerivWithin ℝ i ψ e.source x =
      iteratedFDerivWithin ℝ i (φ ∘ e) e.source x :=
    iteratedFDerivWithin_congr (pullbackChartFun_eqOn e φ) hxU i
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv e.open_source.uniqueDiffOn
    (ψ.contDiff.contDiffAt.of_le (by simp)) hxU, heq]
  let P := (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm ℝ F ℝ ⊤ K)
  calc
    _ ≤ (i.factorial : ℝ) * P φ * B ^ i := by
      apply norm_iteratedFDerivWithin_comp_le (t := Set.univ) φ.contDiff.contDiffOn he
        (by simp) uniqueDiffOn_univ e.open_source.uniqueDiffOn (mapsTo_univ _ _) hxU
      · intro j hji
        rw [iteratedFDerivWithin_univ]
        exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
          (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hji))
      · exact fun j h1 hi => hj x hx j h1 hi
    _ = _ := by ring

private def pullbackChartCompactTestCLM (K : Compacts F) (hK : (K : Set F) ⊆ e.target) :
    𝓓_{K}(F, ℝ) →L[ℝ] 𝓓_{pullbackChartSupport e K hK}(E, ℝ) := by
  let L : 𝓓_{K}(F, ℝ) →ₗ[ℝ] 𝓓_{pullbackChartSupport e K hK}(E, ℝ) :=
    { toFun := pullbackChartCompactTest e he K hK
      map_add' := by
        intro φ ψ
        ext x
        change pullbackChartFun e (⇑(φ + ψ)) x =
          pullbackChartFun e φ x + pullbackChartFun e ψ x
        by_cases hx : x ∈ e.source <;> simp [pullbackChartFun, hx]
      map_smul' := by
        intro c φ
        ext x
        change pullbackChartFun e (⇑(c • φ)) x = c • pullbackChartFun e φ x
        by_cases hx : x ∈ e.source <;> simp [pullbackChartFun, hx] }
  refine ⟨L, continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (ContDiffMapSupportedIn.withSeminorms ..) L (Seminorm.IsBounded.of_real fun i => ?_)⟩
  obtain ⟨C, hC, h⟩ := exists_bound_pullbackChartCompactTest e he K hK i
  refine ⟨Finset.Iic i, C, fun φ => ?_⟩
  exact ((L φ).seminorm_top_le_iff ℝ (mul_nonneg hC (apply_nonneg _ _)) i).2 (h φ)

private def pullbackChartTest (φ : 𝓓(V, ℝ)) : 𝓓(U, ℝ) := by
  let K : Compacts F := ⟨tsupport φ, φ.hasCompactSupport⟩
  have hK : (K : Set F) ⊆ e.target := φ.tsupport_subset
  have hs := support_pullbackChartFun_subset e K hK (subset_tsupport (⇑φ))
  let J := pullbackChartSupport e K hK
  exact ⟨pullbackChartFun e φ, contDiff_pullbackChartFun e he φ.contDiff K hK (subset_tsupport (⇑φ)),
    HasCompactSupport.of_support_subset_isCompact J.isCompact hs,
    (closure_minimal hs J.isCompact.isClosed).trans (pullbackChartSupport_subset e K hK)⟩

/-- Pull back real tests along a smooth open chart and extend by zero off its source. -/
def pullbackChartTestCLM : 𝓓(V, ℝ) →L[ℝ] 𝓓(U, ℝ) :=
  TestFunction.limitCLM ℝ (pullbackChartTest e he)
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ (pullbackChartSupport_subset e K hK)).comp
      (pullbackChartCompactTestCLM e he K hK))
    (fun _ _ _ => rfl)

theorem pullbackChartTestCLM_apply_of_mem (φ : 𝓓(V, ℝ)) {x : E} (hx : x ∈ e.source) :
    pullbackChartTestCLM e he φ x = φ (e x) :=
  pullbackChartFun_eqOn e φ hx

theorem tsupport_pullbackChartTestCLM_subset (φ : 𝓓(V, ℝ)) :
    tsupport (pullbackChartTestCLM e he φ) ⊆ e.symm '' tsupport φ := by
  let K : Compacts F := ⟨tsupport φ, φ.hasCompactSupport⟩
  have hK : (K : Set F) ⊆ e.target := φ.tsupport_subset
  exact closure_minimal (support_pullbackChartFun_subset e K hK (subset_tsupport (⇑φ)))
    (pullbackChartSupport e K hK).isCompact.isClosed

theorem pullbackChartTestCLM_comp_symm (hes : ContDiffOn ℝ ∞ e.symm e.target)
    (φ : 𝓓(U, ℝ)) :
    pullbackChartTestCLM e he (pullbackChartTestCLM e.symm hes φ) = φ := by
  ext x
  by_cases hx : x ∈ e.source
  · calc
      _ = pullbackChartTestCLM e.symm hes φ (e x) := pullbackChartTestCLM_apply_of_mem e he _ hx
      _ = φ (e.symm (e x)) := pullbackChartTestCLM_apply_of_mem e.symm hes φ (e.map_source hx)
      _ = φ x := congrArg φ (e.left_inv hx)
  · exact ((pullbackChartTestCLM e he (pullbackChartTestCLM e.symm hes φ)).zero_on_compl hx).trans
      (φ.zero_on_compl hx).symm

/-- A smooth open chart with smooth inverse identifies the two real test function spaces. -/
def pullbackChartTestEquiv (hes : ContDiffOn ℝ ∞ e.symm e.target) : 𝓓(V, ℝ) ≃L[ℝ] 𝓓(U, ℝ) where
  toLinearEquiv :=
    { (pullbackChartTestCLM e he).toLinearMap with
      invFun := pullbackChartTestCLM e.symm hes
      left_inv := fun φ => pullbackChartTestCLM_comp_symm e.symm hes he φ
      right_inv := pullbackChartTestCLM_comp_symm e he hes }
  continuous_toFun := (pullbackChartTestCLM e he).continuous
  continuous_invFun := (pullbackChartTestCLM e.symm hes).continuous

/-- Transport a complex distribution to the target of a smooth open chart. -/
def pushforwardChartDistribution (D : 𝓓'(U, ℂ)) : 𝓓'(V, ℂ) :=
  D.comp (pullbackChartTestCLM e he)

@[simp]
theorem pushforwardChartDistribution_apply (D : 𝓓'(U, ℂ)) (φ : 𝓓(V, ℝ)) :
    pushforwardChartDistribution e he D φ = D (pullbackChartTestCLM e he φ) := rfl

/-- Restrict a complex distribution to a smaller open subset, by the inclusion
of tests supported in that subset. -/
def restrictOpenDistribution {Ω Ω' : Opens E} (_ : Ω' ≤ Ω) (D : 𝓓'(Ω, ℂ)) : 𝓓'(Ω', ℂ) :=
  D.comp (TestFunction.monoCLM ℝ)

end Langlands.HarmonicAnalysis
