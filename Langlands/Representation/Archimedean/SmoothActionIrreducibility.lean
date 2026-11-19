import Langlands.Representation.Archimedean.SmoothOrbitAveraging
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Topological irreducibility of the genuine smooth action -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R

/-- Closed invariant subspaces for the actual action with its genuine derivative topology. -/
def IsTopologicallyIrreducible : Prop :=
  Nontrivial D ∧ ∀ W : Submodule ℂ D, IsClosed (W : Set D) →
    (∀ g : Aˣ, ∀ v ∈ W, representation 𝓜 R g v ∈ W) → W = ⊥ ∨ W = ⊤

variable [FiniteDimensional ℝ A] [CompleteSpace E]

section Measure

variable [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  (μ : Measure Aˣ) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]

/-- A normalized kernel near the identity approximates a given smooth vector in any
finite collection of its genuine word coordinates. -/
theorem exists_smoothAverage_close_finiteWords (hR : IsContinuousRepresentation R)
    (v : D) (I : Finset (List A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (κ : Aˣ → ℂ) (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ),
      dist (finiteWords R I v) (finiteWords R I
        (smoothAverage R μ hR κ hκ hc (derivativeCoordinates 𝓜 R v []))) < ε := by
  let P := finiteWords R I
  let a := fun g : Aˣ => P (representation 𝓜 R g v)
  have ha : Continuous a := P.continuous.comp
    ((continuous_representation_units R hR).comp (continuous_id.prodMk continuous_const))
  let U : Set Aˣ := {g | ‖a g⁻¹ - P v‖ < ε / 2}
  have hU : U ∈ 𝓝 (1 : Aˣ) := by
    have hh : Continuous (fun g : Aˣ => ‖a g⁻¹ - P v‖) :=
      ((ha.comp continuous_inv).sub continuous_const).norm
    apply hh.continuousAt (gt_mem_nhds ?_)
    simp [a, half_pos hε]
  obtain ⟨κ, hκ, hk, hsupp, hnonneg, -, hκi, hκnorm⟩ :=
    Langlands.Analysis.smoothNormalizedInverseKernel A Aˣ μ U hU
  let f : Aˣ → ℂ := fun g => κ g
  have hf : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ f := Complex.ofRealCLM.contDiff.contMDiff.comp hκ
  have hfc : HasCompactSupport f := hk.comp_left Complex.ofReal_zero
  let w := smoothAverage R μ hR f hf hfc (derivativeCoordinates 𝓜 R v [])
  refine ⟨f, hf, hfc, ?_⟩
  have hi : Integrable (fun g : Aˣ => κ g⁻¹ • a g) μ :=
    ((hκ.continuous.comp continuous_inv).smul ha).integrable_of_hasCompactSupport
      ((hk.comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)
  have hw : P w = ∫ g, κ g⁻¹ • a g ∂μ := by
    funext i
    let L : (I → E) →L[ℂ] E := ContinuousLinearMap.proj i
    change derivativeCoordinates 𝓜 R w i.val = L (∫ g, κ g⁻¹ • a g ∂μ)
    rw [← L.integral_comp_comm hi, derivativeCoordinates_smoothAverage]
    apply integral_congr_ae
    filter_upwards with g
    exact algebraMap_smul ℂ (κ g⁻¹)
      (derivativeCoordinates 𝓜 R (representation 𝓜 R g v) i.val)
  have he : P w - P v = ∫ g, κ g⁻¹ • (a g - P v) ∂μ := by
    simp only [hw, smul_sub, integral_sub hi (hκi.smul_const (P v)), integral_smul_const,
      hκnorm, one_smul]
  have hb : ‖P w - P v‖ ≤ ε / 2 := by
    rw [he]
    calc
      _ ≤ ∫ g, κ g⁻¹ * (ε / 2) ∂μ := by
        apply norm_integral_le_of_norm_le (hκi.mul_const (ε / 2))
        filter_upwards with g
        rw [norm_smul, Real.norm_of_nonneg (hnonneg _)]
        by_cases hg : κ g⁻¹ = 0
        · simp [hg]
        · have hgU : g⁻¹ ∈ U := hsupp (subset_tsupport κ hg)
          have hbound : ‖a g - P v‖ < ε / 2 := by simpa [U] using hgU
          exact mul_le_mul_of_nonneg_left hbound.le (hnonneg _)
      _ = ε / 2 := by rw [integral_mul_const, hκnorm, one_mul]
  rw [dist_comm, dist_eq_norm]
  exact hb.trans_lt (half_lt_self hε)

include μ in
private theorem isTopologicallyIrreducible_of_measure (hR : IsContinuousRepresentation R)
    (hirr : Langlands.Archimedean.IsTopologicallyIrreducible R) : IsTopologicallyIrreducible R := by
  let P := derivativeCLM 𝓜 R []
  have hP : Function.Injective P := by
    intro x y he
    exact (toSmooth 𝓜 R).injective (Subtype.ext he)
  have hP_dense : DenseRange P := by
    have hr : range P = (smoothVectors 𝓜 R : Set E) := by
      ext v
      constructor
      · rintro ⟨w, rfl⟩
        exact (toSmooth 𝓜 R w).property
      · intro hv
        exact ⟨(toSmooth 𝓜 R).symm ⟨v, hv⟩, rfl⟩
    rw [DenseRange, hr]
    exact dense_smoothVectors_units R μ hR
  refine ⟨?_, fun W hW hstable => ?_⟩
  · let : Nontrivial E := hirr.1
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    by_contra hD
    have : Subsingleton D := not_nontrivial_iff_subsingleton.mp hD
    have hsub : range P ⊆ {0} := by
      rintro _ ⟨v, rfl⟩
      rw [Subsingleton.elim v (0 : D), map_zero]
      exact mem_singleton 0
    exact hx (mem_singleton_iff.mp (closure_minimal hsub isClosed_singleton (hP_dense x)))
  let M := W.map P.toLinearMap
  have hM (g : Aˣ) : MapsTo (R g) (M : Set E) M := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨representation 𝓜 R g v, hstable g v hv, rfl⟩
  obtain hb | ht := hirr.2 M.topologicalClosure (Submodule.isClosed_topologicalClosure M)
    (fun g x hx => (hM g).closure (R g).continuous hx)
  · left
    apply le_antisymm ?_ bot_le
    intro v hv
    have hPv : P v ∈ M.topologicalClosure := Submodule.le_topologicalClosure _ ⟨v, hv, rfl⟩
    rw [hb] at hPv
    have he : P v = P 0 := by simpa only [map_zero] using (Submodule.mem_bot ℂ).mp hPv
    exact (Submodule.mem_bot ℂ).mpr (hP he)
  · right
    have hmem (κ : Aˣ → ℂ) (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ) (x : E) :
        smoothAverage R μ hR κ hκ hc x ∈ W := by
      have h : MapsTo (smoothAverage R μ hR κ hκ hc) (M : Set E) W := by
        rintro _ ⟨v, hv, rfl⟩
        exact smoothAverage_mem R μ hR κ hκ hc W hW hstable v hv
      exact h.closure_left (smoothAverage R μ hR κ hκ hc).continuous hW
        (show x ∈ M.topologicalClosure by rw [ht]; exact Submodule.mem_top)
    apply le_antisymm le_top
    intro v _
    change v ∈ (W : Set D)
    rw [← hW.closure_eq, (isEmbedding_derivativeCoordinates 𝓜 R).isInducing.closure_eq_preimage_closure_image]
    apply mem_closure_of_finite_projections
    intro I
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨κ, hκ, hc, hclose⟩ := exists_smoothAverage_close_finiteWords R μ hR v I hε
    let w := smoothAverage R μ hR κ hκ hc (P v)
    exact ⟨finiteWords R I w,
      ⟨derivativeCoordinates 𝓜 R w, ⟨w, hmem κ hκ hc (P v), rfl⟩, rfl⟩, hclose⟩

end Measure

/-- Norm topological irreducibility transfers to the genuine smooth-vector action. -/
theorem isTopologicallyIrreducible_of_norm (hR : IsContinuousRepresentation R)
    (hirr : Langlands.Archimedean.IsTopologicallyIrreducible R) : IsTopologicallyIrreducible R := by
  let : MeasurableSpace Aˣ := borel Aˣ
  let : BorelSpace Aˣ := ⟨rfl⟩
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  exact isTopologicallyIrreducible_of_measure R (Measure.haar : Measure Aˣ) hR hirr

end Langlands.Archimedean.DerivativeSmoothVectors
