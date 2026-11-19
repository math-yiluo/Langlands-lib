import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness
import Langlands.Representation.Archimedean.SmoothUnitAction
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Derivatives of the actual smooth-vector action in the open units chart -/

noncomputable section

open Filter Set Asymptotics
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Analysis

/-- The slope criterion for a real curve in a topological real vector space. -/
theorem hasDerivAt_iff_tendsto_slope_tvs
    {D : Type*} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    [IsTopologicalAddGroup D] [ContinuousSMul ℝ D]
    {f : ℝ → D} {f' : D} {t : ℝ} :
    HasDerivAt f f' t ↔ Tendsto (slope f t) (𝓝[≠] t) (𝓝 f') := by
  let r := fun u => f u - f t - (u - t) • f'
  calc
    HasDerivAt f f' t ↔ Tendsto (fun u => (u - t)⁻¹ • r u) (𝓝 t) (𝓝 0) := by
      simp only [HasDerivAt, HasDerivAtFilter, hasFDerivAtFilter_iff_isLittleOTVS,
        Filter.prod_pure, isLittleOTVS_map, Function.comp_def,
        ContinuousLinearMap.toSpanSingleton_apply]
      exact isLittleOTVS_iff_tendsto_inv_smul (Eventually.of_forall fun u hu => by
        simp [sub_eq_zero.mp hu])
    _ ↔ Tendsto (fun u => (u - t)⁻¹ • r u) (𝓝[≠] t) (𝓝 0) :=
      (tendsto_inf_principal_nhds_iff_of_forall_eq (by simp)).symm
    _ ↔ Tendsto (fun u => slope f t u - f') (𝓝[≠] t) (𝓝 0) := by
      apply tendsto_congr'
      refine (EqOn.eventuallyEq fun u hu => ?_).filter_mono inf_le_right
      change (u - t)⁻¹ • (f u - f t - (u - t) • f') = slope f t u - f'
      rw [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr hu), slope_def_module]
    _ ↔ Tendsto (slope f t) (𝓝[≠] t) (𝓝 f') := by
      rw [← nhds_translation_sub f', tendsto_comap_iff]
      rfl

end Langlands.Analysis

namespace Langlands.Archimedean.DerivativeSmoothVectors

open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)

/-- The open chart of the units given by the ambient algebra value. -/
def unitsValueChart (A : Type*) [NormedRing A] [CompleteSpace A] : OpenPartialHomeomorph Aˣ A :=
  Units.isOpenEmbedding_val.toOpenPartialHomeomorph Units.val

variable {A : Type*} [NormedRing A] [CompleteSpace A]

@[simp]
theorem unitsValueChart_symm_val (g : Aˣ) : (unitsValueChart A).symm (g : A) = g :=
  Units.isOpenEmbedding_val.toOpenPartialHomeomorph_left_inv Units.val

variable [NormedAlgebra ℝ A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "U" => Set.range (Units.val : Aˣ → A)

private theorem contMDiffOn_unitsValueChart_symm :
    ContMDiffOn 𝓜 𝓜 ∞ (unitsValueChart A).symm U :=
  contMDiffOn_isOpenEmbedding_symm (I := 𝓜) Units.isOpenEmbedding_val

/-- The action on the genuine smooth carrier expressed in the open units chart. -/
def unitsChartAction (p : A × D) : D :=
  representation 𝓜 R ((unitsValueChart A).symm p.1) p.2

@[simp]
theorem unitsChartAction_val (g : Aˣ) (v : D) :
    unitsChartAction R (g.val, v) = representation 𝓜 R g v := by
  simp [unitsChartAction]

/-- The ordinary Banach-space derivative of the chart orbit after the empty-word projection. -/
private theorem hasDerivAt_emptyWord_unitsChartAction (g : Aˣ) (v : D)
    {c : ℝ → A} {Y : A} {t : ℝ} (hc : HasDerivAt c Y t) (hct : c t = g.val) :
    HasDerivAt (fun u => derivativeCoordinates 𝓜 R (unitsChartAction R (c u, v)) [])
      (R g (lieDerivative 𝓜 R ((g⁻¹ : Aˣ).val * Y) (toSmooth 𝓜 R v))) t := by
  let F := fun k : Aˣ => R (g * k) (toSmooth 𝓜 R v)
  let f := F ∘ (unitsValueChart A).symm
  let m := ContinuousLinearMap.mul ℝ A (g⁻¹ : Aˣ).val
  have hF : ContMDiff 𝓜 𝓘(ℝ, E) ∞ F :=
    (toSmooth 𝓜 R v).property.comp (contMDiff_const.mul contMDiff_id)
  have hf : DifferentiableAt ℝ f (1 : A) :=
    ((hF.comp_contMDiffOn contMDiffOn_unitsValueChart_symm).contDiffOn.contDiffAt
      (Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨(1 : Aˣ), rfl⟩)).differentiableAt (by simp)
  have hval : mfderiv 𝓜 𝓜 (Units.val : Aˣ → A) (1 : Aˣ) = ContinuousLinearMap.id ℝ A :=
    mfderiv_extChartAt_self (I := 𝓜) (x := (1 : Aˣ))
  have he : F = f ∘ Units.val := by
    funext k
    simp [f]
  have hd : mfderiv 𝓜 𝓘(ℝ, E) F 1 = fderiv ℝ f 1 := by
    rw [he, mfderiv_comp (1 : Aˣ) hf.mdifferentiableAt
      ((Units.contMDiff_val (n := ∞)).mdifferentiableAt (by simp)), hval, mfderiv_eq_fderiv]
    exact ContinuousLinearMap.comp_id _
  have hm : (m ∘ c) t = 1 := by
    change (g⁻¹ : Aˣ).val * c t = 1
    rw [hct, Units.inv_mul]
  have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq t (m.hasFDerivAt.comp_hasDerivAt t hc) hm.symm
  have hD : (fderiv ℝ f 1) (m Y) =
      R g (lieDerivative 𝓜 R ((g⁻¹ : Aˣ).val * Y) (toSmooth 𝓜 R v)) := by
    rw [← hd]
    exact (apply_lieDerivative 𝓜 R g (m Y) (toSmooth 𝓜 R v).property).symm
  apply (hh.congr_deriv hD).congr_of_eventuallyEq
  have hctU : c t ∈ U := by rw [hct]; exact ⟨g, rfl⟩
  have hu : ∀ᶠ u in 𝓝 t, c u ∈ U := hc.continuousAt
    (Units.isOpenEmbedding_val.isOpen_range.mem_nhds hctU)
  filter_upwards [hu] with u hu
  obtain ⟨k, hk⟩ := hu
  have hk' : m (c u) = (g⁻¹ * k : Aˣ).val := by
    change (g⁻¹ : Aˣ).val * c u = _
    rw [← hk, Units.val_mul]
  change R ((unitsValueChart A).symm (c u)) (toSmooth 𝓜 R v) = f (m (c u))
  rw [hk', ← hk, unitsValueChart_symm_val]
  change R k (toSmooth 𝓜 R v) =
    R (g * (unitsValueChart A).symm (↑(g⁻¹ * k) : A)) (toSmooth 𝓜 R v)
  rw [unitsValueChart_symm_val, mul_inv_cancel_left]

variable [FiniteDimensional ℝ A]

/-- Every genuine word coordinate of a smooth-vector orbit is a smooth Banach-valued map. -/
theorem contMDiff_derivativeCoordinates_representation_units (s : List A) (v : D) :
    ContMDiff 𝓜 𝓘(ℝ, E) ∞ (fun g : Aˣ =>
      derivativeCoordinates 𝓜 R (representation 𝓜 R g v) s) := by
  let b := Module.finBasis ℝ A
  simp_rw [derivativeCoordinates_representation_units]
  induction s using List.reverseRecOn generalizing v with
  | nil => exact (toSmooth 𝓜 R v).property
  | append_singleton s X ih =>
      have he (g : Aˣ) : R g (derivativeCoordinates 𝓜 R v
          ((s ++ [X]).map (inverseConjugationCLM g))) =
          ∑ i, b.coord i (inverseConjugationCLM g X) • R g (derivativeCoordinates 𝓜 R
            (operator 𝓜 R (b i) v) (s.map (inverseConjugationCLM g))) := by
        rw [List.map_append, List.map_singleton, ← derivativeCoordinates_operator,
          operator_eq_sum_basis R b]
        let L := ((R g).toLinearMap.comp
          ((derivativeCLM 𝓜 R (s.map (inverseConjugationCLM g))).toLinearMap)).restrictScalars ℝ
        change L (∑ i, b.coord i (inverseConjugationCLM g X) • operator 𝓜 R (b i) v) =
          ∑ i, b.coord i (inverseConjugationCLM g X) • L (operator 𝓜 R (b i) v)
        simp only [map_sum, map_smul]
      simp_rw [he]
      apply contMDiff_finsetSum
      intro i _
      have hc : ContMDiff 𝓜 𝓘(ℝ, ℝ) ∞
          (fun g : Aˣ => b.coord i (inverseConjugationCLM g X)) := by
        refine (b.coord i).toContinuousLinearMap.contDiff.contMDiff.comp ?_
        simp only [inverseConjugationCLM_apply]
        have hm : ContMDiff 𝓘(ℝ, A × A) 𝓜 ∞ (fun p : A × A => p.1 * p.2) :=
          (show ContDiff ℝ ∞ (fun p : A × A => p.1 * p.2) from contDiff_mul).contMDiff
        have hi : ContMDiff 𝓜 𝓜 ∞ (fun g : Aˣ => (g⁻¹ : Aˣ).val) :=
          Units.contMDiff_val.comp (contMDiff_inv 𝓜 ∞)
        exact hm.comp ((hm.comp (hi.prodMk_space (contMDiff_const (c := X)))).prodMk_space
          Units.contMDiff_val)
      exact hc.smul (ih _)

/-- The orbit in the units chart is smooth after any genuine word projection. -/
theorem contDiffOn_derivativeCoordinates_unitsChartAction (s : List A) (v : D) :
    ContDiffOn ℝ ∞ (fun x : A => derivativeCoordinates 𝓜 R (unitsChartAction R (x, v)) s) U :=
  ((contMDiff_derivativeCoordinates_representation_units R s v).comp_contMDiffOn
    contMDiffOn_unitsValueChart_symm).contDiffOn

/-- Differentiating a fixed smooth-vector orbit along a chart curve gives a derivative
in the genuine word topology of the smooth carrier. -/
theorem hasDerivAt_unitsChartOrbit (hR : IsContinuousRepresentation R) (g : Aˣ) (v : D)
    {c : ℝ → A} {Y : A} {t : ℝ} (hc : HasDerivAt c Y t) (hct : c t = g.val) :
    HasDerivAt (fun u => unitsChartAction R (c u, v))
      (representation 𝓜 R g (operator 𝓜 R ((g⁻¹ : Aˣ).val * Y) v)) t := by
  let f := fun u => unitsChartAction R (c u, v)
  let z := representation 𝓜 R g (operator 𝓜 R ((g⁻¹ : Aˣ).val * Y) v)
  let q : List A → E := fun s => deriv (fun u => derivativeCoordinates 𝓜 R (f u) s) t
  have hctU : c t ∈ U := by rw [hct]; exact ⟨g, rfl⟩
  have hq (s : List A) : HasDerivAt (fun u => derivativeCoordinates 𝓜 R (f u) s) (q s) t := by
    have hs := (contDiffOn_derivativeCoordinates_unitsChartAction R s v).contDiffAt
      (Units.isOpenEmbedding_val.isOpen_range.mem_nhds hctU)
    exact ((hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hc).differentiableAt.hasDerivAt
  have hlim : Tendsto (fun u => derivativeCoordinates 𝓜 R (slope f t u)) (𝓝[≠] t) (𝓝 q) := by
    apply tendsto_pi_nhds.mpr
    intro s
    change Tendsto (fun u => derivativeCoordinates 𝓜 R (slope f t u) s) (𝓝[≠] t) (𝓝 (q s))
    have he : (fun u => derivativeCoordinates 𝓜 R (slope f t u) s) =
        slope (fun u => derivativeCoordinates 𝓜 R (f u) s) t := by
      funext u
      rw [slope_def_module, slope_def_module]
      let L := (derivativeCLM 𝓜 R s).restrictScalars ℝ
      change L ((u - t)⁻¹ • (f u - f t)) = (u - t)⁻¹ • (L (f u) - L (f t))
      rw [map_smul, map_sub]
    rw [he]
    exact (hq s).tendsto_slope
  obtain ⟨w, hw⟩ := (isClosed_range_derivativeCoordinates_units R hR).mem_of_tendsto hlim
    (Eventually.of_forall fun u => ⟨slope f t u, rfl⟩)
  have hwz : w = z := by
    apply (toSmooth 𝓜 R).injective
    apply Subtype.ext
    change derivativeCoordinates 𝓜 R w [] = derivativeCoordinates 𝓜 R z []
    rw [hw]
    exact (hq []).unique (hasDerivAt_emptyWord_unitsChartAction R g v hc hct)
  subst w
  exact hasDerivAt_iff_tendsto_slope_tvs.mpr
    ((isEmbedding_derivativeCoordinates 𝓜 R).tendsto_nhds_iff.mpr (hw ▸ hlim))

/-- The chart action is continuous on its open domain in the genuine word topology. -/
theorem continuousOn_unitsChartAction (hR : IsContinuousRepresentation R) :
    ContinuousOn (unitsChartAction R) (U ×ˢ (univ : Set D)) := by
  have hc : ContinuousOn (fun p : A × D => (unitsValueChart A).symm p.1)
      (U ×ˢ (univ : Set D)) := by
    have hu : ContinuousOn (unitsValueChart A).symm U :=
      contMDiffOn_unitsValueChart_symm.continuousOn
    exact hu.comp continuousOn_fst (fun _ h => h.1)
  have hp : ContinuousOn (fun p : A × D => ((unitsValueChart A).symm p.1, p.2))
      (U ×ˢ (univ : Set D)) := hc.prodMk continuousOn_snd
  change ContinuousOn ((fun p : Aˣ × D => representation 𝓜 R p.1 p.2) ∘
    (fun p : A × D => ((unitsValueChart A).symm p.1, p.2))) _
  exact (continuous_representation_units R hR).comp_continuousOn hp

/-- The actual joint action differentiates in the genuine topology along any
real curve with a derivative in each of the chart and vector variables. -/
theorem hasDerivAt_unitsChartAction (hR : IsContinuousRepresentation R) (g : Aˣ)
    {c : ℝ → A} {v : ℝ → D} {Y : A} {W : D} {t : ℝ}
    (hc : HasDerivAt c Y t) (hct : c t = g.val) (hv : HasDerivAt v W t) :
    HasDerivAt (fun u => unitsChartAction R (c u, v u))
      (representation 𝓜 R g (operator 𝓜 R ((g⁻¹ : Aˣ).val * Y) (v t) + W)) t := by
  have hctU : c t ∈ U := by rw [hct]; exact ⟨g, rfl⟩
  have hc' : ContinuousAt (fun u => (unitsValueChart A).symm (c u)) t :=
    ((contMDiffOn_unitsValueChart_symm.continuousOn _ hctU).continuousAt
      (Units.isOpenEmbedding_val.isOpen_range.mem_nhds hctU)).comp hc.continuousAt
  have hgt : (unitsValueChart A).symm (c t) = g := by simp [hct]
  have hg : Tendsto (fun u => (unitsValueChart A).symm (c u)) (𝓝[≠] t) (𝓝 g) :=
    hgt ▸ hc'.tendsto.mono_left nhdsWithin_le_nhds
  have h1 := hasDerivAt_iff_tendsto_slope_tvs.mp (hasDerivAt_unitsChartOrbit R hR g (v t) hc hct)
  have h2 := ((continuous_representation_units R hR).tendsto (g, W)).comp
    (hg.prodMk_nhds (hasDerivAt_iff_tendsto_slope_tvs.mp hv))
  apply hasDerivAt_iff_tendsto_slope_tvs.mpr
  rw [map_add]
  refine (h1.add h2).congr (fun u => ?_)
  simp only [Function.comp_apply, slope_def_module, unitsChartAction]
  let L := (representation 𝓜 R ((unitsValueChart A).symm (c u))).restrictScalars ℝ
  let Lt := (representation 𝓜 R ((unitsValueChart A).symm (c t))).restrictScalars ℝ
  change (u - t)⁻¹ • (L (v t) - Lt (v t)) + L ((u - t)⁻¹ • (v u - v t)) =
    (u - t)⁻¹ • (L (v u) - Lt (v t))
  rw [map_smul, map_sub, ← smul_add]
  congr 1
  abel

end Langlands.Archimedean.DerivativeSmoothVectors
