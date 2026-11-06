import Langlands.Global.LocalModularCharacter.ChartComparison
import Langlands.Global.LocalModularCharacter.LocalScaling

/-! # Modular-character bounds from derivatives in a chart at the identity

Let `φ` be a chart of a topological group `H` at `1` with `φ 1 = 0`.  If the group law read in
the chart is strictly differentiable at `(0, 0)` with derivative `(a, b) ↦ … + b`, and the
conjugation by `g` read in the chart has derivative `A` at `0`, then the modular character of
`g` is at most the Haar scaling factor of `A`.  This holds in two cases: `E` ultrametric, or `E`
a finite-dimensional real normed space. -/

noncomputable section

open MeasureTheory Measure Filter Topology Set Metric
open scoped NNReal ENNReal

namespace Langlands.Global.LocalModularCharacter

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {E : Type*} [NormedAddCommGroup E] (φ : OpenPartialHomeomorph H E)

section GroupLaw

omit [IsTopologicalGroup H] in
theorem chart_symm_zero (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) : φ.symm 0 = 1 := by
  rw [← h0, φ.left_inv h1]

omit [IsTopologicalGroup H] in
theorem tendsto_chart_symm_zero (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) :
    Tendsto φ.symm (𝓝 0) (𝓝 1) := by
  have h0t : (0 : E) ∈ φ.target := h0 ▸ φ.map_source h1
  have := φ.continuousAt_symm h0t
  rwa [ContinuousAt, chart_symm_zero φ h1 h0] at this

omit [IsTopologicalGroup H] in
/-- In the chart, `0` is a right identity of the group law near `0`. -/
theorem chart_mul_zero_eventually (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) :
    ∀ᶠ y in 𝓝 (0 : E), φ (φ.symm y * φ.symm 0) = y := by
  have h0t : (0 : E) ∈ φ.target := h0 ▸ φ.map_source h1
  filter_upwards [φ.eventually_right_inverse h0t] with y hy
  rw [chart_symm_zero φ h1 h0, mul_one, hy]

/-- The inverse read in the chart is continuous at `0`. -/
theorem tendsto_chart_inv (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) :
    Tendsto (fun y => φ ((φ.symm y)⁻¹)) (𝓝 0) (𝓝 0) := by
  have hφ : Tendsto φ (𝓝 1) (𝓝 0) := by
    have := φ.continuousAt h1
    rwa [ContinuousAt, h0] at this
  have hinv : Tendsto (fun y => (φ.symm y)⁻¹) (𝓝 (0 : E)) (𝓝 1) := by
    simpa using (tendsto_chart_symm_zero φ h1 h0).inv
  exact hφ.comp hinv

/-- Left multiplication by the chart inverse undoes left multiplication, near `(0, 0)`. -/
theorem chart_inv_mul_eventually (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) :
    ∀ᶠ p : E × E in 𝓝 0,
      φ (φ.symm (φ ((φ.symm p.1)⁻¹)) * φ.symm (φ (φ.symm p.1 * φ.symm p.2))) = p.2 := by
  have h0t : (0 : E) ∈ φ.target := h0 ▸ φ.map_source h1
  have hs : φ.source ∈ 𝓝 (1 : H) := φ.open_source.mem_nhds h1
  have hfst : Tendsto (fun p : E × E => φ.symm p.1) (𝓝 0) (𝓝 1) :=
    (tendsto_chart_symm_zero φ h1 h0).comp (continuous_fst.tendsto' _ _ rfl)
  have hsnd : Tendsto (fun p : E × E => φ.symm p.2) (𝓝 0) (𝓝 1) :=
    (tendsto_chart_symm_zero φ h1 h0).comp (continuous_snd.tendsto' _ _ rfl)
  have hA : Tendsto (fun p : E × E => (φ.symm p.1)⁻¹) (𝓝 0) (𝓝 1) := by
    simpa using hfst.inv
  have hB : Tendsto (fun p : E × E => φ.symm p.1 * φ.symm p.2) (𝓝 0) (𝓝 1) := by
    simpa using hfst.mul hsnd
  have hC : Tendsto (Prod.snd : E × E → E) (𝓝 0) (𝓝 0) := continuous_snd.tendsto' _ _ rfl
  filter_upwards [hA.eventually_mem hs, hB.eventually_mem hs,
    hC.eventually_mem (φ.open_target.mem_nhds h0t)] with p hpA hpB hpC
  rw [φ.left_inv hpA, φ.left_inv hpB, inv_mul_cancel_left, φ.right_inv hpC]

/-- Left multiplication undoes left multiplication by the chart inverse, near `(0, 0)`. -/
theorem chart_mul_inv_eventually (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) :
    ∀ᶠ p : E × E in 𝓝 0,
      φ (φ.symm p.1 * φ.symm (φ (φ.symm (φ ((φ.symm p.1)⁻¹)) * φ.symm p.2))) = p.2 := by
  have h0t : (0 : E) ∈ φ.target := h0 ▸ φ.map_source h1
  have hs : φ.source ∈ 𝓝 (1 : H) := φ.open_source.mem_nhds h1
  have hfst : Tendsto (fun p : E × E => φ.symm p.1) (𝓝 0) (𝓝 1) :=
    (tendsto_chart_symm_zero φ h1 h0).comp (continuous_fst.tendsto' _ _ rfl)
  have hsnd : Tendsto (fun p : E × E => φ.symm p.2) (𝓝 0) (𝓝 1) :=
    (tendsto_chart_symm_zero φ h1 h0).comp (continuous_snd.tendsto' _ _ rfl)
  have hA : Tendsto (fun p : E × E => (φ.symm p.1)⁻¹) (𝓝 0) (𝓝 1) := by
    simpa using hfst.inv
  have hD : Tendsto (fun p : E × E => (φ.symm p.1)⁻¹ * φ.symm p.2) (𝓝 0) (𝓝 1) := by
    simpa using hfst.inv.mul hsnd
  have hC : Tendsto (Prod.snd : E × E → E) (𝓝 0) (𝓝 0) := continuous_snd.tendsto' _ _ rfl
  filter_upwards [hA.eventually_mem hs, hD.eventually_mem hs,
    hC.eventually_mem (φ.open_target.mem_nhds h0t)] with p hpA hpD hpC
  rw [φ.left_inv hpA, φ.left_inv hpD, mul_inv_cancel_left, φ.right_inv hpC]

end GroupLaw

variable [MeasurableSpace E] [BorelSpace E] (l : Measure E) [IsAddHaarMeasure l]

/-- Ultrametric left-translation estimate in a chart, from strict differentiability of the
group law at `(0, 0)`. -/
theorem chart_translation_ultrametric [IsUltrametricDist E] [ProperSpace E] {K : Type*}
    [NontriviallyNormedField K] [NormedSpace K E] (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0)
    {L : E × E →L[K] E} (hT : HasStrictFDerivAt (fun p : E × E => φ (φ.symm p.1 * φ.symm p.2)) L 0)
    (hL : ∀ w, L (0, w) = w) :
    ∀ η : ℝ≥0, 0 < η → ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ X ⊆ ball (0 : E) r,
      l ((fun z => φ (φ.symm y * φ.symm z)) '' X) ≤ (1 + η) * l X := by
  intro η _
  obtain ⟨r, hr, h⟩ := measure_image_le_of_near_translation_ultrametric l
    (m := fun y z => φ (φ.symm y * φ.symm z)) (ι := fun y => φ ((φ.symm y)⁻¹))
    (near_translation_estimate (m := fun y z => φ (φ.symm y * φ.symm z)) hT hL)
    (chart_mul_zero_eventually φ h1 h0) (tendsto_chart_inv φ h1 h0)
    (chart_inv_mul_eventually φ h1 h0) (chart_mul_inv_eventually φ h1 h0)
  exact ⟨r, hr, fun y hy X hX =>
    (h y hy X hX).trans (le_mul_of_one_le_left (by positivity) le_self_add)⟩

omit [IsTopologicalGroup H] in
/-- Archimedean left-translation estimate in a chart, from strict differentiability of the
group law at `(0, 0)`. -/
theorem chart_translation_real [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Type*}
    [NontriviallyNormedField K] [NormedSpace K E]
    {L : E × E →L[K] E} (hT : HasStrictFDerivAt (fun p : E × E => φ (φ.symm p.1 * φ.symm p.2)) L 0)
    (hL : ∀ w, L (0, w) = w) :
    ∀ η : ℝ≥0, 0 < η → ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ X ⊆ ball (0 : E) r,
      l ((fun z => φ (φ.symm y * φ.symm z)) '' X) ≤ (1 + η) * l X := fun η hη =>
  measure_image_le_of_near_translation l
    (near_translation_estimate (m := fun y z => φ (φ.symm y * φ.symm z)) hT hL) η hη

variable [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

omit [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace E] [BorelSpace E] in
theorem chart_conj_zero (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) (g : H) :
    φ (g * φ.symm 0 * g⁻¹) = 0 := by
  rw [chart_symm_zero φ h1 h0, mul_one, mul_inv_cancel, h0]

/-- **Ultrametric chart bound for the modular character.** -/
theorem modularCharacter_le_of_chart_ultrametric [IsUltrametricDist E] [ProperSpace E]
    {K : Type*} [NontriviallyNormedField K] [NormedSpace K E] (h1 : (1 : H) ∈ φ.source)
    (h0 : φ 1 = 0) {L : E × E →L[K] E}
    (hT : HasStrictFDerivAt (fun p : E × E => φ (φ.symm p.1 * φ.symm p.2)) L 0)
    (hL : ∀ w, L (0, w) = w) (g : H) (A : E ≃L[K] E)
    (hψ : HasFDerivAt (fun z => φ (g * φ.symm z * g⁻¹)) (A : E →L[K] E) 0) (e : E ≃ₜ+ E)
    (he : ∀ x, e x = A x) :
    modularCharacter g ≤ addEquivAddHaarChar e :=
  modularCharacter_le_of_chart addHaar φ h1 h0 g _
    (chart_translation_ultrametric φ addHaar h1 h0 hT hL)
    fun η _ => measure_image_ball_le_of_hasFDerivAt_ultrametric addHaar A e he hψ
      (chart_conj_zero φ h1 h0 g) η

/-- **Archimedean chart bound for the modular character.** -/
theorem modularCharacter_le_of_chart_real [ProperSpace E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Type*} [NontriviallyNormedField K] [NormedSpace K E]
    (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) {L : E × E →L[K] E}
    (hT : HasStrictFDerivAt (fun p : E × E => φ (φ.symm p.1 * φ.symm p.2)) L 0)
    (hL : ∀ w, L (0, w) = w) (g : H) (A : E ≃L[K] E)
    (hψ : HasFDerivAt (fun z => φ (g * φ.symm z * g⁻¹)) (A : E →L[K] E) 0) (e : E ≃ₜ+ E)
    (he : ∀ x, e x = A x) :
    modularCharacter g ≤ addEquivAddHaarChar e :=
  modularCharacter_le_of_chart addHaar φ h1 h0 g _ (chart_translation_real φ addHaar hT hL)
    fun η hη => measure_image_ball_le_of_hasFDerivAt addHaar A e he hψ
      (chart_conj_zero φ h1 h0 g) η hη

end Langlands.Global.LocalModularCharacter
