import Langlands.Representation.Archimedean.SmoothOrbitAveraging

/-! # Closed invariant smooth subspaces are recovered from their Banach closures -/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

universe uA uE

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] (R : Aˣ →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors I R
local notation "ε₀" => derivativeCLM I R []

/-- A closed invariant subspace of the genuine smooth carrier consists of all smooth
vectors whose underlying Banach vectors lie in its norm closure. -/
def SmoothClosedInvariantSaturationStatement : Prop :=
  IsContinuousRepresentation R →
    ∀ W : Submodule ℂ D, IsClosed (W : Set D) →
      (∀ (g : Aˣ) (v : D), v ∈ W → representation I R g v ∈ W) →
      W = (W.map (ε₀).toLinearMap).topologicalClosure.comap (ε₀).toLinearMap

private theorem exists_smoothAverage_near_finiteWords
    [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    (μ : Measure Aˣ) [μ.IsHaarMeasure] (hR : IsContinuousRepresentation R)
    (v : D) (J : Finset (List A)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (κ : Aˣ → ℂ) (hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ),
      ‖finiteWords R J (smoothAverage R μ hR κ hκ hc (ε₀ v)) - finiteWords R J v‖ < δ := by
  let F := finiteWords R J
  let b (g : Aˣ) : J → E := F (representation I R g v)
  have hbc : Continuous b :=
    F.continuous.comp ((continuous_representation_units R hR).comp
      (continuous_id.prodMk continuous_const))
  let U : Set Aˣ := {g | ‖b g⁻¹ - F v‖ < δ / 2}
  have hU : U ∈ 𝓝 (1 : Aˣ) := by
    apply ((hbc.comp continuous_inv).sub continuous_const).norm.continuousAt (gt_mem_nhds ?_)
    simpa [b] using half_pos hδ
  obtain ⟨a, had, hac, haU, ha₀, -, hai, han⟩ :=
    Langlands.Analysis.smoothNormalizedInverseKernel A Aˣ μ U hU
  let κ : Aˣ → ℂ := fun g => a g
  have hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ := Complex.ofRealCLM.contDiff.contMDiff.comp had
  have hc : HasCompactSupport κ := hac.comp_left Complex.ofReal_zero
  let w := smoothAverage R μ hR κ hκ hc (ε₀ v)
  have hbi : Integrable (fun g => a g⁻¹ • b g) μ :=
    ((had.continuous.comp continuous_inv).smul hbc).integrable_of_hasCompactSupport
      ((hac.comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)
  have hw : F w = ∫ g, a g⁻¹ • b g ∂μ := by
    funext i
    let p : (J → E) →L[ℂ] E := ContinuousLinearMap.proj i
    change derivativeCoordinates I R w i.val = p (∫ g, a g⁻¹ • b g ∂μ)
    rw [← p.integral_comp_comm hbi]
    change derivativeCoordinates I R w i.val = ∫ g, a g⁻¹ • b g i ∂μ
    change derivativeCoordinates I R (smoothAverage R μ hR κ hκ hc
      (derivativeCoordinates I R v [])) i.val = _
    rw [derivativeCoordinates_smoothAverage]
    exact integral_congr_ae (Eventually.of_forall fun g =>
      algebraMap_smul ℂ (a g⁻¹) (b g i))
  refine ⟨κ, hκ, hc, ?_⟩
  change ‖F w - F v‖ < δ
  have hsub : F w - F v = ∫ g, a g⁻¹ • (b g - F v) ∂μ := by
    rw [hw]
    simp only [smul_sub, integral_sub hbi (hai.smul_const _), integral_smul_const, han, one_smul]
  rw [hsub]
  calc
    _ ≤ ∫ g, a g⁻¹ * (δ / 2) ∂μ := by
      apply norm_integral_le_of_norm_le (hai.mul_const _)
      filter_upwards with g
      rw [norm_smul, Real.norm_of_nonneg (ha₀ _)]
      by_cases hz : a g⁻¹ = 0
      · simp [hz]
      · have hg : g⁻¹ ∈ U := haU (subset_tsupport a hz)
        have hbound : ‖b g - F v‖ < δ / 2 := by simpa [U] using hg
        exact mul_le_mul_of_nonneg_left hbound.le (ha₀ _)
    _ = δ / 2 := by rw [integral_mul_const, han, one_mul]
    _ < δ := half_lt_self hδ

theorem smoothClosedInvariantSaturation : SmoothClosedInvariantSaturationStatement R := by
  intro hR W hW hWG
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : MeasurableSpace Aˣ := borel Aˣ
  let : BorelSpace Aˣ := ⟨rfl⟩
  let μ := (Measure.haar : Measure Aˣ)
  apply le_antisymm
  · exact fun _ hv => Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hv)
  intro v hv
  let c := derivativeCoordinates I R
  have hc : IsClosedEmbedding c :=
    ⟨isEmbedding_derivativeCoordinates I R, isClosed_range_derivativeCoordinates_units R hR⟩
  have hvW : c v ∈ closure (c '' (W : Set D)) := by
    apply mem_closure_of_finite_projections
    intro J
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨κ, hκ, hcs, hnear⟩ := exists_smoothAverage_near_finiteWords R μ hR v J hδ
    let P := smoothAverage R μ hR κ hκ hcs
    have hPb : (W.map (ε₀).toLinearMap : Set E) ⊆ P ⁻¹' (W : Set D) := by
      rintro _ ⟨w, hw, rfl⟩
      exact smoothAverage_mem R μ hR κ hκ hcs W hW hWG w hw
    have hPw : P (ε₀ v) ∈ W := closure_minimal hPb (hW.preimage P.continuous) hv
    refine ⟨finiteWords R J (P (ε₀ v)), ⟨_, ⟨_, hPw, rfl⟩, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact hnear
  rw [(hc.isClosedMap _ hW).closure_eq] at hvW
  obtain ⟨w, hw, hwv⟩ := hvW
  exact (hc.injective hwv) ▸ hw

end Langlands.Archimedean.DerivativeSmoothVectors
