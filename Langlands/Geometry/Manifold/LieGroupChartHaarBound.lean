import Langlands.Analysis.SmoothLinearDeterminant
import Langlands.Geometry.Manifold.LieGroupEllipticChart
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Local domination of Euclidean chart measure by Lie group Haar measure -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

set_option autoImplicit false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace E H]
  [LieGroup 𝓘(ℝ, E) ∞ H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

local notation "F" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
/-- Near the identity, Euclidean measure transported by the inverse chart is bounded by
left Haar measure times a finite constant. -/
theorem exists_chartVolume_le_smul_haar (μ : Measure H) [μ.IsHaarMeasure] :
    let L : E ≃L[ℝ] F := toEuclidean
    let e := extChartAt 𝓘(ℝ, E) (1 : H)
    let S := L.symm ⁻¹' e.target
    let ψ := e.symm ∘ L.symm
    let x₀ := L (e 1)
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ S ∧ ∃ c : ℝ≥0∞, c ≠ ⊤ ∧
      (volume.restrict (closedBall x₀ R)).map ψ ≤ c • μ := by
  classical
  let L : E ≃L[ℝ] F := toEuclidean
  let e := extChartAt 𝓘(ℝ, E) (1 : H)
  let S := L.symm ⁻¹' e.target
  let ψ := e.symm ∘ L.symm
  let x₀ := L (e 1)
  have he1 : (1 : H) ∈ e.source := mem_extChartAt_source _
  have hs : IsOpen S := (isOpen_extChartAt_target (1 : H)).preimage L.symm.continuous
  have hx₀ : x₀ ∈ S := by
    change L.symm (L (e 1)) ∈ e.target
    rw [L.symm_apply_apply]
    exact e.map_source he1
  have hψ₀ : ψ x₀ = 1 := by
    change e.symm (L.symm (L (e 1))) = 1
    rw [L.symm_apply_apply, e.left_inv he1]
  have heψ {x : F} (hx : x ∈ S) : L (e (ψ x)) = x := by
    change L (e (e.symm (L.symm x))) = x
    rw [e.right_inv hx, L.apply_symm_apply]
  have hψe {a : H} (ha : a ∈ e.source) : ψ (L (e a)) = a := by
    change e.symm (L.symm (L (e a))) = a
    rw [L.symm_apply_apply, e.left_inv ha]
  have hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ S :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (1 : H)).comp
      L.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)
  have heOpen : IsOpen e.source := isOpen_extChartAt_source _
  have heCont : ContinuousOn (L ∘ e) e.source :=
    L.continuous.comp_continuousOn (continuousOn_extChartAt (I := 𝓘(ℝ, E)) (1 : H))
  obtain ⟨R₀, hR₀, hR₀S⟩ := Metric.isOpen_iff.mp hs x₀ hx₀
  let T := closedBall x₀ (R₀ / 2)
  have hTS : T ⊆ S := (closedBall_subset_ball (half_lt_self hR₀)).trans hR₀S
  -- The coordinate transition for small right translations.
  let P : F × F → H := fun z => ψ z.1 * (ψ z.2)⁻¹
  have hP : ContMDiffOn 𝓘(ℝ, F × F) 𝓘(ℝ, E) ∞ P (S ×ˢ S) := by
    have hf : ContMDiffOn 𝓘(ℝ, F × F) 𝓘(ℝ, E) ∞ (fun z : F × F => ψ z.1) (S ×ˢ S) :=
      hψ.comp contDiff_fst.contMDiff.contMDiffOn (fun _ hz => (mem_prod.mp hz).1)
    have hg : ContMDiffOn 𝓘(ℝ, F × F) 𝓘(ℝ, E) ∞ (fun z : F × F => ψ z.2) (S ×ˢ S) :=
      hψ.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => (mem_prod.mp hz).2)
    exact hf.mul hg.inv
  let B := (S ×ˢ S) ∩ P ⁻¹' e.source
  have hBo : IsOpen B := hP.continuousOn.isOpen_inter_preimage (hs.prod hs) heOpen
  have hB₀ : (x₀, x₀) ∈ B := ⟨⟨hx₀, hx₀⟩, by simpa [P, hψ₀] using he1⟩
  let m : F × F → F := fun z => L (e (P z))
  have hm : ContDiffOn ℝ ∞ m B := by
    apply L.contDiff.comp_contDiffOn
    rw [← contMDiffOn_iff_contDiffOn]
    intro z hz
    have hz' : P z ∈ (chartAt E (1 : H)).source := by
      rw [← extChartAt_source (I := 𝓘(ℝ, E))]
      exact hz.2
    exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz').comp z
      ((hP z hz.1).contMDiffAt ((hs.prod hs).mem_nhds hz.1))).contMDiffWithinAt
  let D : F × F → (F →L[ℝ] F) := fun z =>
    (fderiv ℝ m z).comp (ContinuousLinearMap.inl ℝ F F)
  have hpart (x z : F) (hz : (x, z) ∈ B) :
      HasFDerivAt (fun y => m (y, z)) (D (x, z)) x := by
    have hd : DifferentiableAt ℝ m (x, z) :=
      ((hm (x, z) hz).contDiffAt (hBo.mem_nhds hz)).differentiableAt (by simp)
    exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x z)
  have hmid {x : F} (hx : x ∈ S) : m (x, x₀) = x := by
    change L (e (ψ x * (ψ x₀)⁻¹)) = x
    rw [hψ₀, inv_one, mul_one, heψ hx]
  have hD₀ : D (x₀, x₀) = 1 := by
    refine (hpart x₀ x₀ hB₀).unique ?_
    apply (hasFDerivAt_id x₀).congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hx₀] with y hy
    exact hmid hy
  have hD : ContinuousAt D (x₀, x₀) :=
    ((ContinuousLinearMap.compL ℝ F (F × F) F).flip (ContinuousLinearMap.inl ℝ F F)).continuous.continuousAt.comp
      (((hm (x₀, x₀) hB₀).contDiffAt (hBo.mem_nhds hB₀)).continuousAt_fderiv (by simp))
  have hdet : ContinuousAt (fun z => (D z).det) (x₀, x₀) :=
    Langlands.Analysis.contDiff_continuousLinearMap_det.continuous.continuousAt.comp hD
  have hdet₀ : (D (x₀, x₀)).det = 1 := by
    rw [hD₀]
    exact LinearMap.det_id
  have hgood : ∀ᶠ z in 𝓝 (x₀, x₀), z ∈ B ∧ m z ∈ ball x₀ (R₀ / 2) ∧
      (1 / 2 : ℝ) < (D z).det := by
    have hm₀ : m (x₀, x₀) = x₀ := hmid hx₀
    filter_upwards [hBo.mem_nhds hB₀,
      ((hm.continuousOn _ hB₀).continuousAt (hBo.mem_nhds hB₀))
        (by rw [hm₀]; exact ball_mem_nhds _ (half_pos hR₀)),
      hdet (U := Ioi (1 / 2 : ℝ)) (by
        change Ioi (1 / 2 : ℝ) ∈ 𝓝 (D (x₀, x₀)).det
        rw [hdet₀]
        exact Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with z hz hz₁ hz₂
    exact ⟨hz, hz₁, hz₂⟩
  obtain ⟨ε, hε, hεgood⟩ := eventually_nhds_iff_ball.mp hgood
  let R := min (ε / 2) (R₀ / 2)
  have hR : 0 < R := lt_min (half_pos hε) (half_pos hR₀)
  have hRT : closedBall x₀ R ⊆ T := closedBall_subset_closedBall (min_le_right _ _)
  have hRS : closedBall x₀ R ⊆ S := hRT.trans hTS
  have hRε : closedBall x₀ R ⊆ ball x₀ ε :=
    closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hε))
  let W : Set H := e.source ∩ (L ∘ e) ⁻¹' ball x₀ R
  have hWo : IsOpen W := heCont.isOpen_inter_preimage heOpen isOpen_ball
  have hW₁ : (1 : H) ∈ W := ⟨he1, mem_ball_self hR⟩
  have hWpos : μ W ≠ 0 := (hWo.measure_pos μ ⟨1, hW₁⟩).ne'
  have hWsub : W ⊆ ψ '' T := by
    intro a ha
    exact ⟨L (e a), hRT (ball_subset_closedBall ha.2), hψe ha.1⟩
  have hWfin : μ W ≠ ⊤ := ((measure_mono hWsub).trans_lt
    ((isCompact_closedBall x₀ (R₀ / 2)).image_of_continuousOn (hψ.continuousOn.mono hTS)).measure_lt_top).ne
  let ν := volume.restrict T
  let μW := μ.restrict W
  have : IsFiniteMeasure μW := isFiniteMeasure_restrict.mpr hWfin
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  let p := S.piecewise ψ (fun _ => (1 : H))
  have hp : Measurable p :=
    hψ.continuousOn.measurable_piecewise continuous_const.continuousOn hs.measurableSet
  have hpψ {y : F} (hy : y ∈ S) : p y = ψ y := piecewise_eq_of_mem S _ _ hy
  have hmap : (volume.restrict (closedBall x₀ R)).map ψ =
      (volume.restrict (closedBall x₀ R)).map p :=
    Measure.map_congr (ae_restrict_of_forall_mem measurableSet_closedBall fun y hy => (hpψ (hRS hy)).symm)
  let c := ((2 : ℝ≥0∞) * volume T) / μ W
  have hc : c ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) measure_closedBall_lt_top.ne) hWpos
  refine ⟨R, hR, hRS, c, hc, ?_⟩
  rw [hmap]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hp hA, Measure.restrict_apply (hp hA), Measure.smul_apply, smul_eq_mul]
  let C := p ⁻¹' A ∩ closedBall x₀ R
  have hC : MeasurableSet C := (hp hA).inter measurableSet_closedBall
  let I : F × H → ℝ≥0∞ := fun z => A.indicator (fun _ => 1) (p z.1 * z.2)
  have hI : Measurable I := (measurable_const.indicator hA).comp ((hp.comp measurable_fst).mul measurable_snd)
  -- A translated inverse image has at least half the original coordinate volume.
  have hlow (a : H) (ha : a ∈ W) : (2 : ℝ≥0∞)⁻¹ * volume C ≤ ∫⁻ y, I (y, a) ∂ν := by
    let z := L (e a)
    have hza : ψ z = a := hψe ha.1
    have hzε : z ∈ ball x₀ ε := hRε (ball_subset_closedBall ha.2)
    have hpair {y : F} (hy : y ∈ closedBall x₀ R) :
        (y, z) ∈ B ∧ m (y, z) ∈ ball x₀ (R₀ / 2) ∧ (1 / 2 : ℝ) < (D (y, z)).det :=
      hεgood (y, z) (by rw [← ball_prod_same]; exact ⟨hRε hy, hzε⟩)
    let g : F → F := fun y => m (y, z)
    have hg {y : F} (hy : y ∈ closedBall x₀ R) : ψ (g y) = ψ y * a⁻¹ := by
      change ψ (L (e (ψ y * (ψ z)⁻¹))) = _
      rw [hψe (hpair hy).1.2]
      exact congrArg (fun b => ψ y * b⁻¹) hza
    have hinj : InjOn g C := by
      intro y hy y' hy' heq
      have hh := congrArg ψ heq
      rw [hg hy.2, hg hy'.2, mul_right_cancel_iff] at hh
      rw [← heψ (hRS hy.2), ← heψ (hRS hy'.2), hh]
    have himage : g '' C ⊆ (fun y => p y * a) ⁻¹' A ∩ T := by
      rintro _ ⟨y, hy, rfl⟩
      have hyT : g y ∈ T := ball_subset_closedBall (hpair hy.2).2.1
      refine ⟨?_, hyT⟩
      change p (g y) * a ∈ A
      rw [hpψ (hTS hyT), hg hy.2, inv_mul_cancel_right, ← hpψ (hRS hy.2)]
      exact hy.1
    have hchg := lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure F) hC
      (fun y (hy : y ∈ C) => (hpart y z (hpair hy.2).1).hasFDerivWithinAt) hinj
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    calc
      _ = ∫⁻ _ in C, (2 : ℝ≥0∞)⁻¹ ∂volume := by rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ y in C, ENNReal.ofReal |(D (y, z)).det| ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hC] with y hy
        have hy' := (hpair hy.2).2.2
        rw [← hhalf]
        exact ENNReal.ofReal_le_ofReal (hy'.le.trans (le_abs_self _))
      _ = volume (g '' C) := hchg
      _ ≤ volume ((fun y => p y * a) ⁻¹' A ∩ T) := measure_mono himage
      _ = ∫⁻ y, I (y, a) ∂ν := by
        rw [show (fun y => I (y, a)) = fun y => A.indicator (fun _ => (1 : ℝ≥0∞)) (p y * a) from rfl,
          lintegral_indicator_const_comp (hp.mul_const a) hA, one_mul,
          Measure.restrict_apply ((hp.mul_const a) hA)]
  -- Average the volume comparison and use left Haar invariance in the inner integral.
  have htot : ((2 : ℝ≥0∞)⁻¹ * volume C) * μ W ≤ μ A * volume T := by
    calc
      _ = ∫⁻ _ : H, (2 : ℝ≥0∞)⁻¹ * volume C ∂μW := by rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ a : H, ∫⁻ y : F, I (y, a) ∂ν ∂μW := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hWo.measurableSet] with a ha
        exact hlow a ha
      _ = ∫⁻ y : F, ∫⁻ a : H, I (y, a) ∂μW ∂ν :=
        (lintegral_lintegral_swap hI.aemeasurable).symm
      _ ≤ ∫⁻ _ : F, μ A ∂ν := by
        apply lintegral_mono
        intro y
        refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans ?_
        change (∫⁻ a : H, A.indicator (fun _ => (1 : ℝ≥0∞)) (p y * a) ∂μ) ≤ μ A
        calc
          _ = ∫⁻ a : H, A.indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ :=
            (measurePreserving_mul_left μ (p y)).lintegral_comp (measurable_const.indicator hA)
          _ = μ A := by rw [lintegral_indicator_const hA, one_mul]
          _ ≤ μ A := le_rfl
      _ = μ A * volume T := by rw [lintegral_const, Measure.restrict_apply_univ]
  change volume C ≤ c * μ A
  rw [show c * μ A = (μ A * volume T) * 2 / μ W by dsimp [c]; simp only [div_eq_mul_inv]; ac_rfl]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hWpos) (Or.inl hWfin)).mpr
  calc
    volume C * μ W = ((2 : ℝ≥0∞)⁻¹ * volume C * μ W) * 2 := by
      rw [show ((2 : ℝ≥0∞)⁻¹ * volume C * μ W) * 2 =
        ((2 : ℝ≥0∞)⁻¹ * 2) * (volume C * μ W) by ac_rfl,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ (μ A * volume T) * 2 := mul_le_mul' htot le_rfl

end Langlands.Geometry.Manifold
