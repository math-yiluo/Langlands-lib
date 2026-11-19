import Langlands.Representation.Archimedean.BanachOrbitSmoothing
import Langlands.Representation.Archimedean.SmoothRangeOperators
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Kernel averaging in the genuine smooth-vector topology -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E)) (μ : Measure Aˣ) [IsFiniteMeasureOnCompacts μ]

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R

omit [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] in
private theorem integrable_weighted (κ : Aˣ → ℂ) (hκ : Continuous κ) (hc : HasCompactSupport κ)
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] {f : Aˣ → B} (hf : Continuous f) :
    Integrable (fun g => κ g⁻¹ • f g) μ :=
  ((hκ.comp continuous_inv).smul hf).integrable_of_hasCompactSupport
    ((hc.comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)

omit [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] [MeasurableSpace Aˣ]
  [BorelSpace Aˣ] in
private theorem exists_opNorm_bound (hR : IsContinuousRepresentation R) {K : Set Aˣ}
    (hK : IsCompact K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖R g‖ ≤ C := by
  let ops : K → E →L[ℂ] E := fun g => R g.val
  obtain ⟨C, hC⟩ := banach_steinhaus (g := ops) fun v => by
    have h : Continuous (fun g : Aˣ => R g v) := hR.comp (continuous_id.prodMk continuous_const)
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn h.continuousOn
    exact ⟨b, fun g => hb g.val g.property⟩
  exact ⟨max C 0, le_max_right _ _, fun g hg => (hC ⟨g, hg⟩).trans (le_max_left _ _)⟩

/-- A compact continuous kernel defines a bounded operator on the Banach representation. -/
def smoothedOperator (hR : IsContinuousRepresentation R) (κ : Aˣ → ℂ)
    (hκ : Continuous κ) (hc : HasCompactSupport κ) : E →L[ℂ] E := by
  have hi (v : E) : Integrable (fun g => κ g⁻¹ • R g v) μ :=
    integrable_weighted μ κ hκ hc (hR.comp (continuous_id.prodMk continuous_const))
  let T : E →ₗ[ℂ] E :=
    { toFun := smoothedVector R μ κ
      map_add' := fun v w => by
        simp only [smoothedVector, map_add, smul_add, integral_add (hi v) (hi w)]
      map_smul' := fun c v => by
        simp only [smoothedVector, map_smul, RingHom.id_apply, smul_comm _ c, integral_smul] }
  apply T.mkContinuousOfExistsBound
  obtain ⟨C, -, hbound⟩ := exists_opNorm_bound R hR hc.inv
  have hκi : Integrable (fun g => ‖κ g⁻¹‖) μ :=
    (((hκ.comp continuous_inv).norm).integrable_of_hasCompactSupport
      ((hc.comp_homeomorph (Homeomorph.inv Aˣ)).comp_left norm_zero))
  refine ⟨(∫ g, ‖κ g⁻¹‖ ∂μ) * C, fun v => ?_⟩
  change ‖smoothedVector R μ κ v‖ ≤ _
  rw [smoothedVector]
  calc
    _ ≤ ∫ g, ‖κ g⁻¹‖ * (C * ‖v‖) ∂μ := by
      apply norm_integral_le_of_norm_le (hκi.mul_const _)
      filter_upwards with g
      rw [norm_smul]
      by_cases hz : κ g⁻¹ = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left
          (((R g).le_opNorm v).trans (mul_le_mul_of_nonneg_right
            (hbound g (subset_tsupport κ hz)) (norm_nonneg v))) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_assoc]

omit [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] in
@[simp]
theorem smoothedOperator_apply (hR : IsContinuousRepresentation R) (κ : Aˣ → ℂ)
    (hκ : Continuous κ) (hc : HasCompactSupport κ) (v : E) :
    smoothedOperator R μ hR κ hκ hc v = smoothedVector R μ κ v :=
  rfl

variable [μ.IsMulLeftInvariant]

/-- A smooth compact kernel acts continuously from the original Banach representation
into its genuine smooth-vector topology. -/
def smoothAverage (hR : IsContinuousRepresentation R) (κ : Aˣ → ℂ)
    (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ) : E →L[ℂ] D :=
  smoothRangeCLM R hR (smoothedOperator R μ hR κ hκ.continuous hc)
    (isSmoothVector_smoothedVector R μ hR hκ hc)

@[simp]
theorem derivativeCoordinates_smoothAverage_empty (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ) (v : E) :
    derivativeCoordinates 𝓜 R (smoothAverage R μ hR κ hκ hc v) [] = smoothedVector R μ κ v :=
  rfl

/-- Membership in a product closure can be tested on all finite projections. -/
theorem mem_closure_of_finite_projections
    {ι : Type*} {F : Type*} [TopologicalSpace F] {S : Set (ι → F)} {x : ι → F}
    (h : ∀ I : Finset ι, (fun i : I => x i.val) ∈
      closure ((fun y : ι → F => fun i : I => y i.val) '' S)) : x ∈ closure S := by
  classical
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hU
  have hT : Set.pi univ (fun i : I => t i.val) ∈ 𝓝 (fun i : I => x i.val) := by
    rw [nhds_pi]
    exact Filter.pi_mem_pi Set.finite_univ fun i _ => ht i.val
  obtain ⟨y, hyt, hy⟩ := mem_closure_iff_nhds.mp (h I) _ hT
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨z, hsub ?_, hz⟩
  intro i hi
  exact hyt ⟨i, hi⟩ (mem_univ _)

/-- Select a finite family of genuine word coordinates in a normed product. -/
def finiteWords (I : Finset (List A)) : D →L[ℂ] (I → E) :=
  ContinuousLinearMap.pi fun i => derivativeCLM 𝓜 R i.val

private theorem integral_mem_closed_submodule
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (M : Submodule ℂ B) (hM : IsClosed (M : Set B)) {f : Ω → B}
    (hf : Integrable f ν) (hmem : ∀ᵐ g ∂ν, f g ∈ M) : (∫ g, f g ∂ν) ∈ M := by
  have : IsClosed (M : Set B) := hM
  apply (Submodule.Quotient.mk_eq_zero M).mp
  change M.mkQL (∫ g, f g ∂ν) = 0
  rw [← M.mkQL.integral_comp_comm hf]
  exact integral_eq_zero_of_ae (hmem.mono fun g hg => (Submodule.Quotient.mk_eq_zero M).mpr hg)

private theorem smoothAverage_spec (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ)
    (W : Submodule ℂ D) (hW : IsClosed (W : Set D))
    (hstable : ∀ (g : Aˣ) (v : D), v ∈ W → representation 𝓜 R g v ∈ W)
    (v : D) (hv : v ∈ W) :
    smoothAverage R μ hR κ hκ hc (derivativeCoordinates 𝓜 R v []) ∈ W ∧
    ∀ s : List A, derivativeCoordinates 𝓜 R
      (smoothAverage R μ hR κ hκ hc (derivativeCoordinates 𝓜 R v [])) s =
      ∫ g, κ g⁻¹ • derivativeCoordinates 𝓜 R (representation 𝓜 R g v) s ∂μ := by
  classical
  let q : List A → E := fun s => ∫ g, κ g⁻¹ •
    derivativeCoordinates 𝓜 R (representation 𝓜 R g v) s ∂μ
  let α := derivativeCoordinates 𝓜 R
  have hr : IsClosedEmbedding α := ⟨isEmbedding_derivativeCoordinates 𝓜 R,
    isClosed_range_derivativeCoordinates_units R hR⟩
  have hq : q ∈ α '' (W : Set D) := by
    rw [← (hr.isClosedMap _ hW).closure_eq]
    apply mem_closure_of_finite_projections
    intro I
    let P := finiteWords R I
    let f : Aˣ → (I → E) := fun g => κ g⁻¹ • P (representation 𝓜 R g v)
    have hcont : Continuous (fun g : Aˣ => P (representation 𝓜 R g v)) :=
      P.continuous.comp ((continuous_representation_units R hR).comp
        (continuous_id.prodMk continuous_const))
    have hfi : Integrable f μ := integrable_weighted μ κ hκ.continuous hc hcont
    have he : (fun i : I => q i.val) = ∫ g, f g ∂μ := by
      funext i
      let p : (I → E) →L[ℂ] E := ContinuousLinearMap.proj i
      change q i.val = p (∫ g, f g ∂μ)
      rw [← p.integral_comp_comm hfi]
      rfl
    rw [he]
    have hm : (∫ g, f g ∂μ) ∈ (W.map P.toLinearMap).topologicalClosure := by
      apply integral_mem_closed_submodule μ _ (Submodule.isClosed_topologicalClosure _) hfi
      apply Eventually.of_forall
      intro g
      apply Submodule.smul_mem
      apply Submodule.le_topologicalClosure
      exact Submodule.mem_map_of_mem (hstable g v hv)
    change (∫ g, f g ∂μ) ∈ closure (P '' (W : Set D)) at hm
    rw [image_image]
    change (∫ g, f g ∂μ) ∈ closure (P '' (W : Set D))
    exact hm
  obtain ⟨w, hw, he⟩ := hq
  let z := smoothAverage R μ hR κ hκ hc (α v [])
  have hwz : w = z := by
    apply (toSmooth 𝓜 R).injective
    apply Subtype.ext
    change α w [] = α z []
    rw [he]
    exact (derivativeCoordinates_smoothAverage_empty R μ hR κ hκ hc (α v [])).symm
  subst w
  exact ⟨hw, fun s => congrFun he s⟩

/-- Averaging a smooth vector commutes with each genuine derivative coordinate
of the weighted translated orbit. -/
theorem derivativeCoordinates_smoothAverage (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ)
    (v : D) (s : List A) : derivativeCoordinates 𝓜 R
      (smoothAverage R μ hR κ hκ hc (derivativeCoordinates 𝓜 R v [])) s =
      ∫ g, κ g⁻¹ • derivativeCoordinates 𝓜 R (representation 𝓜 R g v) s ∂μ :=
  (smoothAverage_spec R μ hR κ hκ hc ⊤ isClosed_univ
    (fun _ _ _ => Submodule.mem_top) v Submodule.mem_top).2 s

/-- Compact smooth averaging preserves closed invariant subspaces of the genuine smooth carrier. -/
theorem smoothAverage_mem (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : ContMDiff 𝓜 𝓘(ℝ, ℂ) ∞ κ) (hc : HasCompactSupport κ)
    (W : Submodule ℂ D) (hW : IsClosed (W : Set D))
    (hstable : ∀ (g : Aˣ) (v : D), v ∈ W → representation 𝓜 R g v ∈ W)
    (v : D) (hv : v ∈ W) :
    smoothAverage R μ hR κ hκ hc (derivativeCoordinates 𝓜 R v []) ∈ W :=
  (smoothAverage_spec R μ hR κ hκ hc W hW hstable v hv).1

end Langlands.Archimedean.DerivativeSmoothVectors
