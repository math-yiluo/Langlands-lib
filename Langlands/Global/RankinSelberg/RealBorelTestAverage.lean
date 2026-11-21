import Langlands.Global.RankinSelberg.RealWhittakerTranslationDistribution
import Langlands.Global.RankinSelberg.RealGodementSmooth
import Langlands.Group.GL.UpperTriangularCartan

/-! # Averaging real matrix tests along the upper triangular group -/

noncomputable section

open Filter Set TopologicalSpace MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis
open scoped ContDiff Distributions Matrix.Norms.Operator Pointwise Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBorelTestAverage

open RealBruhatDistributionRestriction

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "Test" => 𝓓(invertibleDomain r, ℂ)

local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace

/-- The compact lift of the matrix test support to the general linear group. -/
def supportLift (f : Test) : Set G := Units.val ⁻¹' tsupport f

theorem isCompact_supportLift (f : Test) : IsCompact (supportLift f) :=
  RealGodement.isCompact_val_preimage f.hasCompactSupport fun _ h => f.tsupport_subset h

/-- One compact integration set works for every output in a compact family. -/
def integrationSupport (f : Test) (L : Set G) : Set B :=
  Subtype.val ⁻¹' (supportLift f * L⁻¹)

theorem isCompact_integrationSupport (f : Test) {L : Set G} (hL : IsCompact L) :
    IsCompact (integrationSupport f L) :=
  (isClosed_upperTriangularSubgroup (r + 1) ℝ).isClosedEmbedding_subtypeVal.isCompact_preimage
    ((isCompact_supportLift f).mul hL.inv)

theorem notMem_tsupport_of_outside_integrationSupport (f : Test) {L : Set G} {g : G} (hg : g ∈ L)
    {b : B} (hb : b ∉ integrationSupport f L) : b.val.val * g.val ∉ tsupport f :=
  fun h => hb ⟨b.val * g, h, g⁻¹, Set.mem_inv.mpr hg, mul_inv_cancel_right b.val g⟩

private theorem exists_open_uniform_integrationSupport (f : Test) {X : M}
    (hX : X ∈ invertibleDomain r) :
    ∃ S : Set M, IsOpen S ∧ X ∈ S ∧
      ∃ L : Set B, IsCompact L ∧ ∀ Y ∈ S, ∀ b ∉ L, b.val.val * Y ∉ tsupport f := by
  obtain ⟨g, rfl⟩ := hX
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds g
  refine ⟨Units.val '' interior C, Units.isOpenEmbedding_val.isOpenMap _ isOpen_interior,
    ⟨g, mem_interior_iff_mem_nhds.mpr hC, rfl⟩, integrationSupport f C,
      isCompact_integrationSupport f hCc, ?_⟩
  rintro Y ⟨y, hy, rfl⟩ b hb
  exact notMem_tsupport_of_outside_integrationSupport f (interior_subset hy) hb

/-- Upper triangular averaging in the actual matrix variable, with a continuous weight. -/
def borelAverage (μ : Measure B) (weight : B → ℂ) (f : Test) (X : M) : ℂ :=
  ∫ b : B, weight b * f (b.val.val * X) ∂μ

theorem integrable_averageIntegrand (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (f : Test) (X : M) :
    Integrable (fun b : B => weight b * f (b.val.val * X)) μ := by
  have hcont : Continuous (fun b : B => weight b * f (b.val.val * X)) :=
    hweight.mul (f.contDiff.continuous.comp ((Units.continuous_val.comp continuous_subtype_val).mul continuous_const))
  apply hcont.integrable_of_hasCompactSupport
  by_cases hX : X ∈ invertibleDomain r
  · obtain ⟨g, rfl⟩ := hX
    refine (isCompact_integrationSupport f (isCompact_singleton (x := g))).of_isClosed_subset
      (isClosed_tsupport _) (closure_minimal ?_ (isCompact_integrationSupport f isCompact_singleton).isClosed)
    intro b hb
    by_contra hb'
    apply hb
    change weight b * f (b.val.val * g.val) = 0
    rw [image_eq_zero_of_notMem_tsupport
      (notMem_tsupport_of_outside_integrationSupport f (mem_singleton g) hb'), mul_zero]
  · have he : (fun b : B => weight b * f (b.val.val * X)) = 0 := by
      funext b
      have hz : f (b.val.val * X) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        obtain ⟨u, hu⟩ := f.tsupport_subset h
        apply hX
        refine ⟨b.val⁻¹ * u, ?_⟩
        rw [Units.val_mul, hu, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_mul]
      simp [hz]
    rw [he]
    exact HasCompactSupport.zero

private def leftLinear (b : B) : M →L[ℝ] M :=
  ContinuousLinearMap.mul ℝ M b.val.val

private theorem continuous_leftLinear : Continuous (leftLinear (r := r)) :=
  (ContinuousLinearMap.mul ℝ M).continuous.comp (Units.continuous_val.comp continuous_subtype_val)

private theorem average_eventuallyEq_compactIntegral (μ : Measure B) (weight : B → ℂ) (f : Test)
    {S : Set M} {L : Set B} (hS : IsOpen S) {X : M} (hXS : X ∈ S)
    (hzero : ∀ Y ∈ S, ∀ b ∉ L, b.val.val * Y ∉ tsupport f) :
    (borelAverage μ weight f) =ᶠ[𝓝 X] fun Y => ∫ b in L, weight b * f (leftLinear b Y) ∂μ := by
  filter_upwards [hS.mem_nhds hXS] with Y hY
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro b hb
  change weight b * f (b.val.val * Y) = 0
  rw [image_eq_zero_of_notMem_tsupport (hzero Y hY b hb), mul_zero]

theorem contDiffOn_borelAverage (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (f : Test) :
    ContDiffOn ℝ ∞ (borelAverage μ weight f) (invertibleDomain r) := by
  intro X hX
  obtain ⟨S, hS, hXS, L, hL, hzero⟩ := exists_open_uniform_integrationSupport f hX
  have hd := (Langlands.Analysis.compactLinearParameterIntegral B M M μ L hL
    S hS univ isOpen_univ weight hweight leftLinear continuous_leftLinear f f.contDiff.contDiffOn
    (fun _ _ _ _ => mem_univ _)).1
  have he := average_eventuallyEq_compactIntegral μ weight f hS hXS hzero
  exact ((hd.contDiffAt (hS.mem_nhds hXS)).congr_of_eventuallyEq he).contDiffWithinAt

/-- Differentiate a matrix test in the infinitesimal right translation direction. -/
def rightDerivativeTest (Y : M) (f : Test) : Test :=
  smoothVectorFieldDerivativeTest (V := (LinearMap.mulRight ℝ Y).toContinuousLinearMap)
    (LinearMap.mulRight ℝ Y).toContinuousLinearMap.contDiff.contDiffOn f

@[simp]
theorem rightDerivativeTest_apply (Y : M) (f : Test) (X : M) :
    rightDerivativeTest Y f X = fderiv ℝ f X (X * Y) := rfl

theorem tsupport_rightDerivativeTest_subset (Y : M) (f : Test) :
    tsupport (rightDerivativeTest Y f) ⊆ tsupport f :=
  tsupport_smoothVectorFieldDerivativeTest_subset _ f

/-- Right differentiation commutes with the upper triangular averaging. -/
theorem fderiv_borelAverage_mul_right (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (f : Test) {X : M}
    (hX : X ∈ invertibleDomain r) (Y : M) :
    fderiv ℝ (borelAverage μ weight f) X (X * Y) =
      borelAverage μ weight (rightDerivativeTest Y f) X := by
  obtain ⟨S, hS, hXS, L, hL, hzero⟩ := exists_open_uniform_integrationSupport f hX
  have hd := (Langlands.Analysis.compactLinearParameterIntegral B M M μ L hL
    S hS univ isOpen_univ weight hweight leftLinear continuous_leftLinear f f.contDiff.contDiffOn
    (fun _ _ _ _ => mem_univ _)).2 X hXS
  have he := average_eventuallyEq_compactIntegral μ weight f hS hXS hzero
  rw [(hd.congr_of_eventuallyEq he).fderiv]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ (f : M → ℂ)) := f.contDiff.fderiv_right (by simp)
  have hcont : Continuous fun b : B => weight b •
      ((fderiv ℝ f (leftLinear b X)).comp (leftLinear b)) :=
    hweight.smul ((hdf.continuous.comp
      (continuous_leftLinear.clm_apply continuous_const)).clm_comp continuous_leftLinear)
  rw [ContinuousLinearMap.integral_apply (hcont.continuousOn.integrableOn_compact (μ := μ) hL)]
  change (∫ b in L, weight b * fderiv ℝ f (b.val.val * X) (b.val.val * (X * Y)) ∂μ) =
    borelAverage μ weight (rightDerivativeTest Y f) X
  simp only [borelAverage, rightDerivativeTest_apply, Matrix.mul_assoc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro b hb
  rw [fderiv_of_notMem_tsupport ℝ (hzero X hXS b hb), zero_apply, mul_zero]

theorem borelAverage_add (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (f h : Test) (X : M) :
    borelAverage μ weight (f + h) X = borelAverage μ weight f X + borelAverage μ weight h X := by
  simp only [borelAverage, add_apply, mul_add]
  exact integral_add (integrable_averageIntegrand μ hweight f X) (integrable_averageIntegrand μ hweight h X)

theorem borelAverage_smul (μ : Measure B) (weight : B → ℂ) (c : ℂ) (f : Test) (X : M) :
    borelAverage μ weight (c • f) X = c * borelAverage μ weight f X := by
  simp only [borelAverage]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with b
  change weight b * (c * f (b.val.val * X)) = c * (weight b * f (b.val.val * X))
  exact mul_left_comm _ _ _

/-- The inverse of a group character is the weight for induced sections. -/
def inverseWeight (χ : B →* ℂˣ) (b : B) : ℂ := (χ b)⁻¹.val

theorem continuous_inverseWeight (χ : B →* ℂˣ) (hχ : Continuous χ) :
    Continuous (inverseWeight χ) := Units.continuous_val.comp hχ.inv

/-- Right Haar integration gives the inducing character on the output's left Borel argument. -/
theorem borelAverage_left_covariance (μ : Measure B) [μ.IsMulRightInvariant]
    (χ : B →* ℂˣ) (f : Test) (b₀ : B) (X : M) :
    borelAverage μ (inverseWeight χ) f (b₀.val.val * X) =
      (χ b₀ : ℂ) * borelAverage μ (inverseWeight χ) f X := by
  have hχ (b : B) : inverseWeight χ b = (χ b₀ : ℂ) * inverseWeight χ (b * b₀) :=
    congrArg Units.val (by rw [map_mul]; group :
      (χ b)⁻¹ = χ b₀ * (χ (b * b₀))⁻¹)
  let F (b : B) := (χ b₀ : ℂ) * (inverseWeight χ b * f (b.val.val * X))
  simp only [borelAverage]
  rw [← integral_const_mul]
  change _ = ∫ b, F b ∂μ
  rw [← integral_mul_right_eq_self F b₀]
  apply integral_congr_ae
  filter_upwards with b
  change inverseWeight χ b * f (b.val.val * (b₀.val.val * X)) =
    (χ b₀ : ℂ) * (inverseWeight χ (b * b₀) * f ((b.val * b₀.val).val * X))
  rw [hχ b, Units.val_mul, Matrix.mul_assoc, mul_assoc]

/-- Averaging a matrix test and translating the output on the right commute. -/
theorem borelAverage_right_pullback (μ : Measure B) (weight : B → ℂ)
    (f h : Test) (g : G) (hfg : ∀ X, h X = f (X * g.val)) (X : M) :
    borelAverage μ weight h X = borelAverage μ weight f (X * g.val) := by
  unfold borelAverage
  apply integral_congr_ae
  filter_upwards with b
  rw [hfg, Matrix.mul_assoc]

private theorem inverseWeight_left_translate (χ : B →* ℂˣ) (u b : B) :
    inverseWeight χ b = (χ u : ℂ) * inverseWeight χ (u * b) :=
  congrArg Units.val (by rw [map_mul, mul_comm (χ u) (χ b), mul_inv_rev, ← mul_assoc,
    mul_inv_cancel, one_mul] : (χ b)⁻¹ = χ u * (χ (u * b))⁻¹)

/-- Left translation on the test gives the inducing character when that
translation preserves the chosen right Haar measure. -/
theorem borelAverage_left_pullback (μ : Measure B) (χ : B →* ℂˣ)
    (f h : Test) (u : B) (hu : μ.map (u * ·) = μ)
    (hfg : ∀ X, h X = f (u.val.val * X)) (X : M) :
    borelAverage μ (inverseWeight χ) h X =
      (χ u : ℂ) * borelAverage μ (inverseWeight χ) f X := by
  let F (b : B) := (χ u : ℂ) * (inverseWeight χ b * f (b.val.val * X))
  have htrans : (∫ b, F (u * b) ∂μ) = ∫ b, F b ∂μ := by
    rw [← (measurableEmbedding_mulLeft u).integral_map, hu]
  simp only [borelAverage]
  rw [← integral_const_mul]
  change _ = ∫ b, F b ∂μ
  rw [← htrans]
  apply integral_congr_ae
  filter_upwards with b
  change inverseWeight χ b * h (b.val.val * X) =
      (χ u : ℂ) * (inverseWeight χ (u * b) * f ((u.val * b.val).val * X))
  rw [hfg, inverseWeight_left_translate χ u b, Units.val_mul, Matrix.mul_assoc, mul_assoc]

/-- Borel averaging produces a smooth left-covariant function on the open
set of invertible real matrices. -/
def RealBorelTestAverageStatement : Prop :=
  ∀ (r : ℕ) (μ : Measure (upperTriangularSubgroup (r + 1) ℝ))
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (χ : upperTriangularSubgroup (r + 1) ℝ →* ℂˣ), Continuous χ →
    ∀ f : 𝓓(invertibleDomain r, ℂ),
      ContDiffOn ℝ ∞ (borelAverage μ (inverseWeight χ) f) (invertibleDomain r) ∧
      ∀ (b₀ : upperTriangularSubgroup (r + 1) ℝ) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
        borelAverage μ (inverseWeight χ) f (b₀.val.val * X) =
          (χ b₀ : ℂ) * borelAverage μ (inverseWeight χ) f X

theorem realBorelTestAverage : RealBorelTestAverageStatement := by
  intro r μ _ _ χ hχ f
  exact ⟨contDiffOn_borelAverage μ (continuous_inverseWeight χ hχ) f,
    borelAverage_left_covariance μ χ f⟩

end Langlands.Global.RankinSelbergGlobal.RealBorelTestAverage
