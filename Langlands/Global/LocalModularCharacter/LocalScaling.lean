import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Local Haar-measure estimates for nearly linear maps

Estimates on small balls of a normed additive group `E` with an additive Haar measure:
nearly-translation families do not increase measure by more than a factor `1 + η`, and a map
with derivative `A` at `0` sends small balls to sets of measure at most `(1 + η)` times the
Haar scaling factor of `A` times the measure of the ball.  Both the archimedean case (a real
finite-dimensional structure on `E`) and the ultrametric case are treated. -/

open MeasureTheory Measure Metric Set Filter Topology
open scoped NNReal ENNReal

namespace Langlands.Global.LocalModularCharacter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The Haar measure of the image under a continuous additive automorphism. -/
theorem measure_image_eq_addEquivAddHaarChar_mul [LocallyCompactSpace E] (μ : Measure E)
    [IsAddHaarMeasure μ] [Regular μ] (e : E ≃ₜ+ E) (Y : Set E) :
    μ (e '' Y) = addEquivAddHaarChar e * μ Y := by
  have h := addEquivAddHaarChar_smul_preimage μ (X := e '' Y) e
  rw [e.injective.preimage_image] at h
  rw [← h, ENNReal.smul_def, smul_eq_mul]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A strict derivative at `(0, 0)` whose restriction to the second factor is the identity
gives a uniform near-translation estimate in the second variable. -/
theorem near_translation_estimate {K : Type*} [NontriviallyNormedField K] [NormedSpace K E]
    {m : E → E → E} {L : E × E →L[K] E} (hm : HasStrictFDerivAt (fun p : E × E => m p.1 p.2) L 0)
    (hL : ∀ w, L (0, w) = w) :
    ∀ δ > 0, ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ z ∈ ball (0 : E) r, ∀ z' ∈ ball (0 : E) r,
      ‖m y z - m y z' - (z - z')‖ ≤ δ * ‖z - z'‖ := by
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hm.isLittleO.def hδ)
  refine ⟨r, hr, fun y hy z hz z' hz' => ?_⟩
  rw [mem_ball_zero_iff] at hy hz hz'
  have hmem : (((y, z), (y, z')) : (E × E) × (E × E)) ∈ ball ((0 : E × E), (0 : E × E)) r := by
    rw [mem_ball, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right]
    exact max_lt (max_lt hy hz) (max_lt hy hz')
  have h := hball hmem
  simp only [Set.mem_ofPred_eq, Prod.mk_sub_mk, sub_self] at h
  rwa [hL, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at h

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `ψ 0 = 0` and `ψ` has derivative `A` at `0`, then `ψ` maps small balls into the image
under `A` of slightly larger balls. -/
theorem image_ball_subset_of_hasFDerivAt {K : Type*} [NontriviallyNormedField K]
    [NormedSpace K E] {ψ : E → E} (A : E ≃L[K] E) (hψ : HasFDerivAt ψ (A : E →L[K] E) 0)
    (h0 : ψ 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ > 0, ∀ r ≤ r₀, ψ '' ball 0 r ⊆ A '' ball 0 ((1 + ε) * r) := by
  set C := ‖(A.symm : E →L[K] E)‖
  have hC : 0 ≤ C := norm_nonneg _
  have hc : 0 < ε / (C + 1) := div_pos hε (by positivity)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1 (hψ.isLittleO.def hc)
  refine ⟨r₀, hr₀, fun r hr => ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hest : ‖ψ z - A z‖ ≤ ε / (C + 1) * ‖z‖ := by
    simpa [h0] using hball (ball_subset_ball hr hz)
  set u := A.symm (ψ z - A z)
  have hu : ‖u‖ ≤ ε * ‖z‖ := by
    calc ‖u‖ ≤ C * ‖ψ z - A z‖ := by
          exact (A.symm : E →L[K] E).le_opNorm (ψ z - A z)
      _ ≤ C * (ε / (C + 1) * ‖z‖) := by gcongr
      _ = C / (C + 1) * (ε * ‖z‖) := by ring
      _ ≤ 1 * (ε * ‖z‖) := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = ε * ‖z‖ := one_mul _
  refine ⟨z + u, ?_, ?_⟩
  · rw [mem_ball_zero_iff] at hz ⊢
    calc ‖z + u‖ ≤ ‖z‖ + ε * ‖z‖ := (norm_add_le _ _).trans (by linarith)
      _ = (1 + ε) * ‖z‖ := by ring
      _ < (1 + ε) * r := by gcongr
  · simp [u]

section Real

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]

/-- Archimedean near-translation estimate: maps uniformly close to translations in the
Lipschitz sense increase the Haar measure of subsets of a small ball by at most `1 + η`. -/
theorem measure_image_le_of_near_translation {m : E → E → E}
    (hm : ∀ δ > 0, ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ z ∈ ball (0 : E) r, ∀ z' ∈ ball (0 : E) r,
      ‖m y z - m y z' - (z - z')‖ ≤ δ * ‖z - z'‖)
    (η : ℝ≥0) (hη : 0 < η) :
    ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ X ⊆ ball (0 : E) r, μ (m y '' X) ≤ (1 + η) * μ X := by
  have hdet : ENNReal.ofReal |(ContinuousLinearMap.id ℝ E).det| < ((1 + η : ℝ≥0) : ℝ≥0∞) := by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one,
      ENNReal.ofReal_one, ENNReal.coe_add, ENNReal.coe_one]
    exact ENNReal.lt_add_right ENNReal.one_ne_top (by exact_mod_cast hη.ne')
  obtain ⟨δ, hδ, hδpos⟩ :=
    ((addHaar_image_le_mul_of_det_lt μ _ hdet).and self_mem_nhdsWithin).exists
  obtain ⟨r, hr, hest⟩ := hm δ (by exact_mod_cast hδpos)
  refine ⟨r, hr, fun y hy X hX => ?_⟩
  have h := hδ X (m y) (fun z hz z' hz' => by simpa using hest y hy z (hX hz) z' (hX hz'))
  simpa using h

/-- Archimedean determinant estimate on small balls. -/
theorem measure_image_ball_le_of_hasFDerivAt [ProperSpace E] {K : Type*}
    [NontriviallyNormedField K] [NormedSpace K E] {ψ : E → E} (A : E ≃L[K] E) (e : E ≃ₜ+ E)
    (he : ∀ x, e x = A x) (hψ : HasFDerivAt ψ (A : E →L[K] E) 0) (h0 : ψ 0 = 0)
    (η : ℝ≥0) (hη : 0 < η) :
    ∃ r₀ > 0, ∀ r ≤ r₀,
      μ (ψ '' ball 0 r) ≤ (1 + η) * addEquivAddHaarChar e * μ (ball 0 r) := by
  set n := Module.finrank ℝ E
  have hlim : Tendsto (fun ε : ℝ => (1 + ε) ^ n) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => (1 + ε) ^ n) := by fun_prop
    simpa using hc.tendsto 0
  have h1 : (1 : ℝ) < 1 + η := by
    have : (0 : ℝ) < η := by exact_mod_cast hη
    linarith
  obtain ⟨ε₀, hε₀, hεball⟩ := Metric.mem_nhds_iff.1 (hlim.eventually (gt_mem_nhds h1))
  set ε := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  have hεn : (1 + ε) ^ n < 1 + η := by
    have : ε ∈ ball (0 : ℝ) ε₀ := by
      rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hε]
      exact half_lt_self hε₀
    exact hεball this
  obtain ⟨r₀, hr₀, hsub⟩ := image_ball_subset_of_hasFDerivAt A hψ h0 hε
  refine ⟨r₀, hr₀, fun r hr => ?_⟩
  have heA : ⇑e = ⇑A := funext he
  have hscale : ENNReal.ofReal ((1 + ε) ^ n) ≤ 1 + (η : ℝ≥0∞) := by
    rw [show (1 : ℝ≥0∞) + η = ENNReal.ofReal (1 + η) by
      rw [ENNReal.ofReal_add zero_le_one η.coe_nonneg, ENNReal.ofReal_one,
        ENNReal.ofReal_coe_nnreal]]
    exact ENNReal.ofReal_le_ofReal hεn.le
  calc μ (ψ '' ball 0 r) ≤ μ (A '' ball 0 ((1 + ε) * r)) := measure_mono (hsub r hr)
    _ = addEquivAddHaarChar e * μ (ball 0 ((1 + ε) * r)) := by
        rw [← heA, measure_image_eq_addEquivAddHaarChar_mul μ e]
    _ = addEquivAddHaarChar e * (ENNReal.ofReal ((1 + ε) ^ n) * μ (ball 0 r)) := by
        rw [addHaar_ball_mul_of_pos μ 0 (by linarith) r]
    _ ≤ addEquivAddHaarChar e * ((1 + η) * μ (ball 0 r)) := by gcongr
    _ = (1 + η) * addEquivAddHaarChar e * μ (ball 0 r) := by ring

end Real

section Ultrametric

variable [IsUltrametricDist E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `ψ 0 = 0` and `ψ` has derivative `A` at `0`, then in an ultrametric space `ψ` maps
small balls into their images under `A`. -/
theorem image_ball_subset_of_hasFDerivAt_ultrametric {K : Type*} [NontriviallyNormedField K]
    [NormedSpace K E] {ψ : E → E} (A : E ≃L[K] E) (hψ : HasFDerivAt ψ (A : E →L[K] E) 0)
    (h0 : ψ 0 = 0) :
    ∃ r₀ > 0, ∀ r ≤ r₀, ψ '' ball 0 r ⊆ A '' ball 0 r := by
  set C := ‖(A.symm : E →L[K] E)‖
  have hC : 0 ≤ C := norm_nonneg _
  have hc : 0 < (C + 1)⁻¹ := inv_pos.2 (by positivity)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1 (hψ.isLittleO.def hc)
  refine ⟨r₀, hr₀, fun r hr => ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hest : ‖ψ z - A z‖ ≤ (C + 1)⁻¹ * ‖z‖ := by
    simpa [h0] using hball (ball_subset_ball hr hz)
  set u := A.symm (ψ z - A z)
  have hu : ‖u‖ ≤ ‖z‖ := by
    calc ‖u‖ ≤ C * ‖ψ z - A z‖ := by
          exact (A.symm : E →L[K] E).le_opNorm (ψ z - A z)
      _ ≤ C * ((C + 1)⁻¹ * ‖z‖) := by gcongr
      _ = C / (C + 1) * ‖z‖ := by ring
      _ ≤ 1 * ‖z‖ := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = ‖z‖ := one_mul _
  refine ⟨z + u, ?_, ?_⟩
  · rw [mem_ball_zero_iff] at hz ⊢
    exact (IsUltrametricDist.norm_add_le_max z u).trans_lt (max_lt hz (hu.trans_lt hz))
  · simp [u]

variable [ProperSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

/-- Ultrametric determinant estimate on small balls. -/
theorem measure_image_ball_le_of_hasFDerivAt_ultrametric {K : Type*}
    [NontriviallyNormedField K] [NormedSpace K E] {ψ : E → E} (A : E ≃L[K] E) (e : E ≃ₜ+ E)
    (he : ∀ x, e x = A x) (hψ : HasFDerivAt ψ (A : E →L[K] E) 0) (h0 : ψ 0 = 0)
    (η : ℝ≥0) :
    ∃ r₀ > 0, ∀ r ≤ r₀,
      μ (ψ '' ball 0 r) ≤ (1 + η) * addEquivAddHaarChar e * μ (ball 0 r) := by
  obtain ⟨r₀, hr₀, hsub⟩ := image_ball_subset_of_hasFDerivAt_ultrametric A hψ h0
  refine ⟨r₀, hr₀, fun r hr => ?_⟩
  have heA : ⇑e = ⇑A := funext he
  calc μ (ψ '' ball 0 r) ≤ μ (A '' ball 0 r) := measure_mono (hsub r hr)
    _ = 1 * addEquivAddHaarChar e * μ (ball 0 r) := by
        rw [one_mul, ← heA, measure_image_eq_addEquivAddHaarChar_mul μ e]
    _ ≤ (1 + η) * addEquivAddHaarChar e * μ (ball 0 r) := by gcongr; exact le_self_add

omit [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- In an ultrametric space, closed balls form a π-system. -/
theorem isPiSystem_closedBalls : IsPiSystem {S : Set E | ∃ x r, S = closedBall x r} := by
  rintro _ ⟨x, r, rfl⟩ _ ⟨y, s, rfl⟩ ⟨w, hwx, hwy⟩
  rw [IsUltrametricDist.closedBall_eq_of_mem hwx, IsUltrametricDist.closedBall_eq_of_mem hwy]
  rcases le_total r s with h | h
  · exact ⟨w, r, inter_eq_left.2 (closedBall_subset_closedBall h)⟩
  · exact ⟨w, s, inter_eq_right.2 (closedBall_subset_closedBall h)⟩

omit [ProperSpace E] in
/-- In a second-countable ultrametric space, closed balls generate the Borel σ-algebra. -/
theorem measurableSpace_eq_generateFrom_closedBalls [SecondCountableTopology E] :
    ‹MeasurableSpace E› = MeasurableSpace.generateFrom {S : Set E | ∃ x r, S = closedBall x r} := by
  apply le_antisymm
  · have hB : TopologicalSpace.IsTopologicalBasis
        {S : Set E | ∃ x, ∃ r > 0, S = closedBall x r} := by
      refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
      · rintro _ ⟨x, r, hr, rfl⟩
        exact IsUltrametricDist.isOpen_closedBall x hr.ne'
      · intro a u hau hu
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu a hau
        exact ⟨closedBall a (ε / 2), ⟨a, ε / 2, half_pos hε, rfl⟩,
          mem_closedBall_self (half_pos hε).le,
          (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
    rw [BorelSpace.measurable_eq (α := E), hB.borel_eq_generateFrom]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨x, r, -, rfl⟩
    exact ⟨x, r, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨x, r, rfl⟩
    exact measurableSet_closedBall

omit [IsUltrametricDist E] [ProperSpace E] in
/-- A map that is isometric on a closed ball, extended by the identity, is measurable. -/
theorem measurable_piecewise_closedBall {c : E} {ρ : ℝ} {h : E → E}
    [DecidablePred (· ∈ closedBall c ρ)]
    (hiso : ∀ z ∈ closedBall c ρ, ∀ z' ∈ closedBall c ρ, dist (h z) (h z') = dist z z') :
    Measurable ((closedBall c ρ).piecewise h id) := by
  have hcont : ContinuousOn h (closedBall c ρ) := by
    refine LipschitzOnWith.continuousOn (K := 1) fun z hz z' hz' => ?_
    rw [edist_dist, edist_dist, hiso z hz z' hz', ENNReal.coe_one, one_mul]
  exact hcont.measurable_piecewise continuousOn_id measurableSet_closedBall

/-- An isometric self-surjection of a closed ball, extended by the identity outside the ball,
preserves the restriction of an additive Haar measure to that ball. -/
theorem map_piecewise_restrict_closedBall {c : E} {ρ : ℝ} {h : E → E}
    [DecidablePred (· ∈ closedBall c ρ)]
    (hmaps : MapsTo h (closedBall c ρ) (closedBall c ρ))
    (hsurj : SurjOn h (closedBall c ρ) (closedBall c ρ))
    (hiso : ∀ z ∈ closedBall c ρ, ∀ z' ∈ closedBall c ρ, dist (h z) (h z') = dist z z') :
    (μ.restrict (closedBall c ρ)).map ((closedBall c ρ).piecewise h id) =
      μ.restrict (closedBall c ρ) := by
  have hmeas : Measurable ((closedBall c ρ).piecewise h id) := measurable_piecewise_closedBall hiso
  have : IsFiniteMeasure (μ.restrict (closedBall c ρ)) :=
    isFiniteMeasure_restrict.2 (measure_closedBall_lt_top (μ := μ)).ne
  refine ext_of_generate_finite _ measurableSpace_eq_generateFrom_closedBalls
    isPiSystem_closedBalls ?_ ?_
  · rintro _ ⟨x, r, rfl⟩
    rw [map_apply hmeas measurableSet_closedBall,
      Measure.restrict_apply (hmeas measurableSet_closedBall),
      Measure.restrict_apply measurableSet_closedBall]
    have hpre : ((closedBall c ρ).piecewise h id) ⁻¹' closedBall x r ∩ closedBall c ρ =
        h ⁻¹' closedBall x r ∩ closedBall c ρ := by
      ext z
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [piecewise_eq_of_mem _ _ _ h2] at h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [piecewise_eq_of_mem _ _ _ h2], h2⟩
    rw [hpre]
    rcases (closedBall x r ∩ closedBall c ρ).eq_empty_or_nonempty with hempty | ⟨w, hwx, hwB⟩
    · have hempty' : h ⁻¹' closedBall x r ∩ closedBall c ρ = ∅ := by
        refine eq_empty_iff_forall_notMem.2 ?_
        rintro z ⟨hz1, hz2⟩
        exact eq_empty_iff_forall_notMem.1 hempty (h z) ⟨hz1, hmaps hz2⟩
      rw [hempty', hempty]
    · rw [IsUltrametricDist.closedBall_eq_of_mem hwx]
      have hBw : closedBall c ρ = closedBall w ρ := IsUltrametricDist.closedBall_eq_of_mem hwB
      rcases le_total ρ r with hρr | hrρ
      · have hsub : closedBall c ρ ⊆ closedBall w r := hBw ▸ closedBall_subset_closedBall hρr
        rw [inter_eq_right.2 hsub, inter_eq_right.2
          (show closedBall c ρ ⊆ h ⁻¹' closedBall w r from fun z hz => hsub (hmaps hz))]
      · obtain ⟨z₀, hz₀B, rfl⟩ := hsurj hwB
        have hB0 : closedBall c ρ = closedBall z₀ ρ := IsUltrametricDist.closedBall_eq_of_mem hz₀B
        have hpre' : h ⁻¹' closedBall (h z₀) r ∩ closedBall c ρ = closedBall z₀ r := by
          ext z
          constructor
          · rintro ⟨hz1, hz2⟩
            rw [mem_closedBall, ← hiso z hz2 z₀ hz₀B]
            exact hz1
          · intro hz
            have hzB : z ∈ closedBall c ρ := hB0 ▸ closedBall_subset_closedBall hrρ hz
            refine ⟨?_, hzB⟩
            rw [mem_preimage, mem_closedBall, hiso z hzB z₀ hz₀B]
            exact hz
        rw [hpre', inter_eq_left.2 (hBw ▸ closedBall_subset_closedBall hrρ),
          addHaar_closedBall_center μ z₀, addHaar_closedBall_center μ (h z₀)]
  · rw [map_apply hmeas MeasurableSet.univ, preimage_univ]

/-- Ultrametric Haar comparison: if `f` maps a closed ball isometrically into itself and has an
inverse `h` on that ball which also maps the ball into itself, then `f` does not increase the
Haar measure of subsets of the ball. -/
theorem measure_image_le_of_isometry_closedBall {c : E} {ρ : ℝ} {f h : E → E}
    (hf : MapsTo f (closedBall c ρ) (closedBall c ρ))
    (hh : MapsTo h (closedBall c ρ) (closedBall c ρ))
    (hhf : ∀ z ∈ closedBall c ρ, h (f z) = z) (hfh : ∀ z ∈ closedBall c ρ, f (h z) = z)
    (hiso : ∀ z ∈ closedBall c ρ, ∀ z' ∈ closedBall c ρ, dist (f z) (f z') = dist z z')
    {X : Set E} (hX : X ⊆ closedBall c ρ) : μ (f '' X) ≤ μ X := by
  classical
  set B := closedBall c ρ with hBdef
  have hisoh : ∀ z ∈ B, ∀ z' ∈ B, dist (h z) (h z') = dist z z' := by
    intro z hz z' hz'
    rw [← hiso _ (hh hz) _ (hh hz'), hfh z hz, hfh z' hz']
  have hsurj : SurjOn h B B := fun z hz => ⟨f z, hf hz, hhf z hz⟩
  have hmap := map_piecewise_restrict_closedBall μ hh hsurj hisoh
  have hmeas : Measurable (B.piecewise h id) := measurable_piecewise_closedBall hisoh
  set M := toMeasurable μ X
  have hM : MeasurableSet M := measurableSet_toMeasurable μ X
  have hsub : f '' X ⊆ (B.piecewise h id) ⁻¹' M ∩ B := by
    rintro _ ⟨x, hx, rfl⟩
    have hxB := hX hx
    refine ⟨?_, hf hxB⟩
    rw [mem_preimage, piecewise_eq_of_mem _ _ _ (hf hxB), hhf x hxB]
    exact subset_toMeasurable μ X hx
  calc μ (f '' X) ≤ μ ((B.piecewise h id) ⁻¹' M ∩ B) := measure_mono hsub
    _ = (μ.restrict B).map (B.piecewise h id) M := by
        rw [map_apply hmeas hM, restrict_apply (hmeas hM)]
    _ = μ.restrict B M := by rw [hmap]
    _ ≤ μ M := restrict_apply_le _ _
    _ = μ X := measure_toMeasurable X

omit [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- In an ultrametric space, a map whose increments are within half their size of the
increments of the identity is isometric. -/
theorem dist_eq_of_near_translation {f : E → E} {z z' : E}
    (h : ‖f z - f z' - (z - z')‖ ≤ 1 / 2 * ‖z - z'‖) : dist (f z) (f z') = dist z z' := by
  rw [dist_eq_norm, dist_eq_norm]
  rcases eq_or_ne z z' with rfl | hne
  · simp
  have hpos : 0 < ‖z - z'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hlt : ‖f z - f z' - (z - z')‖ < ‖z - z'‖ := by linarith
  have heq := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  rw [sub_add_cancel, max_eq_right hlt.le] at heq
  exact heq

/-- Ultrametric near-translation estimate: a family of maps uniformly close to translations,
which fixes `0` up to translation and is closed under two-sided inverses near `0`, does not
increase the Haar measure of subsets of a small ball. -/
theorem measure_image_le_of_near_translation_ultrametric {m : E → E → E} {ι : E → E}
    (hm : ∀ δ > 0, ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ z ∈ ball (0 : E) r, ∀ z' ∈ ball (0 : E) r,
      ‖m y z - m y z' - (z - z')‖ ≤ δ * ‖z - z'‖)
    (hm0 : ∀ᶠ y in 𝓝 (0 : E), m y 0 = y) (hι : Tendsto ι (𝓝 0) (𝓝 0))
    (hinv : ∀ᶠ p : E × E in 𝓝 0, m (ι p.1) (m p.1 p.2) = p.2)
    (hinv' : ∀ᶠ p : E × E in 𝓝 0, m p.1 (m (ι p.1) p.2) = p.2) :
    ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ X ⊆ ball (0 : E) r, μ (m y '' X) ≤ μ X := by
  obtain ⟨r₁, hr₁, hm1⟩ := hm (1 / 2) (by norm_num)
  obtain ⟨r₂, hr₂, h0⟩ := Metric.eventually_nhds_iff_ball.1 hm0
  obtain ⟨r₃, hr₃, hi⟩ := Metric.eventually_nhds_iff_ball.1 hinv
  obtain ⟨r₄, hr₄, hi'⟩ := Metric.eventually_nhds_iff_ball.1 hinv'
  set ρ := min (min r₁ r₂) (min r₃ r₄) with hρ
  have hρpos : 0 < ρ := lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄)
  obtain ⟨rι, hrι, hιb⟩ := Metric.tendsto_nhds_nhds.1 hι ρ hρpos
  set s := min ρ rι / 2 with hs
  have hspos : 0 < s := by positivity
  have hsρ : s < ρ := by
    have := min_le_left ρ rι
    linarith
  have hsι : s < rι := by
    have := min_le_right ρ rι
    linarith
  have hρ1 : ρ ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ r₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ r₄ := (min_le_right _ _).trans (min_le_right _ _)
  have hB : ∀ {w : E}, ‖w‖ ≤ s → ∀ k, ρ ≤ k → w ∈ ball (0 : E) k := fun hw k hk => by
    rw [mem_ball_zero_iff]
    linarith
  have hpair : ∀ {w w' : E}, ‖w‖ ≤ s → ‖w'‖ ≤ s → ∀ k, ρ ≤ k →
      ((w, w') : E × E) ∈ ball (0 : E × E) k := fun hw hw' k hk => by
    rw [mem_ball_zero_iff, Prod.norm_def]
    exact max_lt (by linarith) (by linarith)
  -- every small parameter gives an isometric self-map of the closed ball of radius `s`
  have hgood : ∀ w : E, ‖w‖ ≤ s →
      MapsTo (m w) (closedBall 0 s) (closedBall 0 s) ∧
      ∀ z ∈ closedBall (0 : E) s, ∀ z' ∈ closedBall (0 : E) s,
        dist (m w z) (m w z') = dist z z' := by
    intro w hw
    have hw1 := hB hw r₁ hρ1
    refine ⟨fun z hz => ?_, fun z hz z' hz' => ?_⟩
    · rw [mem_closedBall_zero_iff] at hz ⊢
      have hz1 := hB hz r₁ hρ1
      have hest := hm1 w hw1 z hz1 0 (hB (by simpa using hspos.le) r₁ hρ1)
      rw [h0 w (hB hw r₂ hρ2), sub_zero] at hest
      have hdecomp : m w z = (m w z - w - z) + (w + z) := by abel
      rw [hdecomp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by linarith) ?_)
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hw hz)
    · rw [mem_closedBall_zero_iff] at hz hz'
      exact dist_eq_of_near_translation (hm1 w hw1 z (hB hz r₁ hρ1) z' (hB hz' r₁ hρ1))
  refine ⟨s, hspos, fun y hy X hX => ?_⟩
  have hys : ‖y‖ ≤ s := (mem_ball_zero_iff.1 hy).le
  have hιy : ι y ∈ ball (0 : E) ρ := hιb (x := y) (by rw [dist_zero_right]; linarith)
  -- the inverse parameter is no larger than `y`
  have hιs : ‖ι y‖ ≤ s := by
    have hι1 : ι y ∈ ball (0 : E) r₁ := ball_subset_ball hρ1 hιy
    have hest := hm1 (ι y) hι1 y (hB hys r₁ hρ1) 0 (hB (by simpa using hspos.le) r₁ hρ1)
    have hy0 : m y 0 = y := h0 y (hB hys r₂ hρ2)
    have hz : m (ι y) y = 0 := by
      have := hi (y, 0) (hpair hys (by simpa using hspos.le) r₃ hρ3)
      simpa [hy0] using this
    rw [hz, h0 (ι y) (ball_subset_ball hρ2 hιy), sub_zero, zero_sub] at hest
    have hdecomp : ι y = -((-ι y - y) + y) := by abel
    rw [hdecomp, norm_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hys)
    have := norm_nonneg y
    linarith
  have hBX : X ⊆ closedBall (0 : E) s := hX.trans ball_subset_closedBall
  refine measure_image_le_of_isometry_closedBall μ (hgood y hys).1 (hgood (ι y) hιs).1
    (fun z hz => ?_) (fun z hz => ?_) (hgood y hys).2 hBX
  · rw [mem_closedBall_zero_iff] at hz
    exact hi (y, z) (hpair hys hz r₃ hρ3)
  · rw [mem_closedBall_zero_iff] at hz
    exact hi' (y, z) (hpair hys hz r₄ hρ4)

end Ultrametric

end Langlands.Global.LocalModularCharacter
