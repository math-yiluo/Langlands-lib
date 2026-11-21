import Langlands.Representation.Archimedean.GardingDensity

/-! # Genuine derivative seminorm bounds for Gårding averages -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

namespace Langlands.Archimedean

universe uA uG uE

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  [LieGroup 𝓘(ℝ, A) ∞ G]

/-- The derivative of the left-translated kernel in the orbit parameter. -/
def gardingKernelDerivative (X : A) (φ : G → ℂ) (y : G) : ℂ :=
  mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun g => φ (g⁻¹ * y)) 1 X

/-- A smooth kernel stays smooth under this genuine differentiation. -/
theorem contMDiff_gardingKernelDerivative (X : A) {φ : G → ℂ}
    (hφ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ) :
    ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ (gardingKernelDerivative X φ) := by
  have hf : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A)) 𝓘(ℝ, ℂ) ∞
      (fun p : G × G => φ (p.2⁻¹ * p.1)) :=
    hφ.comp (contMDiff_snd.inv.mul contMDiff_fst)
  intro y₀
  have hd := (hf.contMDiffAt (x := (y₀, (1 : G)))).mfderiv_apply (m := ∞) (x₀ := y₀)
    (fun y g : G => φ (g⁻¹ * y)) (fun _ : G => (1 : G))
    (fun y : G => y) (fun _ : G => X)
    contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
  have hc : ∀ y : G,
      inTangentCoordinates 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun _ : G => (1 : G))
        (fun y : G => φ (1⁻¹ * y))
        (fun y : G => mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun g => φ (g⁻¹ * y)) 1)
        y₀ y = mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun g => φ (g⁻¹ * y)) 1 := by
    intro y
    rw [inTangentCoordinates_eq]
    · rw [tangentBundleCore_coordChange_model_space]
      have hself : (tangentBundleCore 𝓘(ℝ, A) G).coordChange
          (achart A (1 : G)) (achart A (1 : G)) 1 = ContinuousLinearMap.id ℝ A := by
        ext Y
        exact tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, A)) (1 : G))
      rw [hself, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · exact mem_chart_source A (1 : G)
    · simp
  simp_rw [hc] at hd
  exact hd

/-- The derivative kernel vanishes off the original closed support. -/
theorem tsupport_gardingKernelDerivative_subset (X : A) (φ : G → ℂ) :
    tsupport (gardingKernelDerivative X φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  by_contra hnot
  have hmul : Continuous (fun g : G => g⁻¹ * y) :=
    ((contMDiff_id.inv.mul contMDiff_const : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞
      (fun g : G => g⁻¹ * y))).continuous
  have h₁ : (1 : G)⁻¹ * y ∈ (tsupport φ)ᶜ := by
    rw [inv_one, one_mul]
    change y ∉ closure (Function.support φ)
    exact hnot
  have hnear : ∀ᶠ g in 𝓝 (1 : G), g⁻¹ * y ∈ (tsupport φ)ᶜ :=
    hmul.continuousAt (isClosed_closure.isOpen_compl.mem_nhds h₁)
  have heq : (fun g => φ (g⁻¹ * y)) =ᶠ[𝓝 (1 : G)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hnear] with g hg
    by_contra hg'
    exact hg (subset_closure hg')
  apply hy
  unfold gardingKernelDerivative
  rw [heq.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
  rfl

/-- The successive derivatives of the compact kernel in a real Lie algebra word. -/
def gardingKernelWord : List A → (G → ℂ) → G → ℂ
  | [], φ => φ
  | X :: Xs, φ => gardingKernelDerivative X (gardingKernelWord Xs φ)

theorem tsupport_gardingKernelWord_subset (Xs : List A) (φ : G → ℂ) :
    tsupport (gardingKernelWord Xs φ) ⊆ tsupport φ := by
  induction Xs with
  | nil => exact Subset.rfl
  | cons X Xs ih =>
      exact (tsupport_gardingKernelDerivative_subset X (gardingKernelWord Xs φ)).trans ih

theorem gardingKernelWord_smooth_compact (Xs : List A) {φ : G → ℂ}
    (hφ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ) (hc : HasCompactSupport φ) :
    ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ (gardingKernelWord Xs φ) ∧
      HasCompactSupport (gardingKernelWord Xs φ) := by
  induction Xs with
  | nil => exact ⟨hφ, hc⟩
  | cons X Xs ih =>
      exact ⟨contMDiff_gardingKernelDerivative X ih.1,
        ih.2.of_isClosed_subset isClosed_closure (tsupport_gardingKernelDerivative_subset X _)⟩

variable [FiniteDimensional ℝ A] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)

include hπ in
/-- Every genuine representation word acts on the translated kernel of
the same actual Bochner average. -/
theorem iteratedLieDerivative_gardingIntegral (φ : G → ℂ)
    (hφ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ) (hc : HasCompactSupport φ) (v : E) (Xs : List A) :
    iteratedLieDerivative 𝓘(ℝ, A) π Xs (∫ x, φ x • π x v ∂μ) =
      ∫ x, gardingKernelWord Xs φ x • π x v ∂μ := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
      rw [iteratedLieDerivative_cons, ih]
      have h := gardingKernelWord_smooth_compact Xs hφ hc
      exact lieDerivative_gardingIntegral μ π hπ _ h.1 h.2 v X

include hπ in
/-- Each genuine word seminorm on the image of one kernel is bounded
by its differentiated kernel's `L¹` norm and the original vector norm. -/
theorem norm_iteratedLieDerivative_gardingIntegral_le
    (hunitary : ∀ g v, ‖π g v‖ = ‖v‖) (φ : G → ℂ)
    (hφ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ) (hc : HasCompactSupport φ) (v : E) (Xs : List A) :
    ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs (∫ x, φ x • π x v ∂μ)‖ ≤
      (∫ x, ‖gardingKernelWord Xs φ x‖ ∂μ) * ‖v‖ := by
  rw [iteratedLieDerivative_gardingIntegral μ π hπ φ hφ hc v Xs]
  calc
    ‖∫ x, gardingKernelWord Xs φ x • π x v ∂μ‖ ≤
      ∫ x, ‖gardingKernelWord Xs φ x • π x v‖ ∂μ := norm_integral_le_integral_norm _
    _ = _ := by simp_rw [norm_smul, hunitary, integral_mul_const]

/-- A derivative-continuous functional gives a bound uniform in the
kernel through finitely many genuine word-derivative `L¹` seminorms. -/
theorem exists_gardingFunctional_L1_bound (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ) :
    ∃ (S : Finset (List A)) (C : ℝ), 0 ≤ C ∧
      ∀ (φ : G → ℂ) (hφ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ)
        (hc : HasCompactSupport φ) (v : E),
        ‖ℓ ⟨∫ x, φ x • π x v ∂μ, isSmoothVector_gardingIntegral μ π hπ φ hφ hc v⟩‖ ≤
          (C * ∑ Xs ∈ S, ∫ x, ‖gardingKernelWord Xs φ x‖ ∂μ) * ‖v‖ := by
  obtain ⟨S, C, hC⟩ := hℓ
  let c := max 0 C
  have hc0 : 0 ≤ c := le_max_left _ _
  refine ⟨S, c, hc0, fun φ hφ hc v => ?_⟩
  let B (Xs : List A) : ℝ := ∫ x, ‖gardingKernelWord Xs φ x‖ ∂μ
  let w : smoothVectors 𝓘(ℝ, A) π :=
    ⟨∫ x, φ x • π x v ∂μ, isSmoothVector_gardingIntegral μ π hπ φ hφ hc v⟩
  change ‖ℓ w‖ ≤ _
  calc
    _ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs w‖ := hC w
    _ ≤ c * ∑ Xs ∈ S, ‖iteratedLieDerivative 𝓘(ℝ, A) π Xs w‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ ≤ c * ∑ Xs ∈ S, B Xs * ‖v‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun Xs _ =>
        norm_iteratedLieDerivative_gardingIntegral_le μ π hπ hunitary φ hφ hc v Xs) hc0
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

/-- A derivative-continuous functional followed by a fixed Gårding
average has a bound in the original norm of the input vector. -/
theorem exists_norm_gardingFunctional_le (hunitary : ∀ g v, ‖π g v‖ = ‖v‖)
    (φ : G → ℂ) (hφ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ) (hc : HasCompactSupport φ)
    (ℓ : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors 𝓘(ℝ, A) π ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E,
      ‖ℓ ⟨∫ x, φ x • π x v ∂μ, isSmoothVector_gardingIntegral μ π hπ φ hφ hc v⟩‖ ≤ C * ‖v‖ := by
  obtain ⟨S, C, hC, h⟩ := exists_gardingFunctional_L1_bound μ π hπ hunitary ℓ hℓ
  exact ⟨C * ∑ Xs ∈ S, ∫ x, ‖gardingKernelWord Xs φ x‖ ∂μ,
    mul_nonneg hC (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _),
    h φ hφ hc⟩

end Langlands.Archimedean
