import Langlands.Global.RankinSelberg.RealBorelTestAverage
import Langlands.Global.RankinSelberg.RealLocalWhittakerProperties

/-! # Continuous compact derivative coordinates of Borel averages -/

noncomputable section

open Filter Set TopologicalSpace MeasureTheory Langlands.Archimedean Langlands.GeneralLinear
open scoped BoundedContinuousFunction ContDiff Distributions Manifold Matrix.Norms.Operator Pointwise Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBorelAverageContinuity

open RealBruhatDistributionRestriction RealBorelTestAverage

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "Test" => 𝓓(invertibleDomain r, ℂ)

local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance (L : Compacts G) : CompactSpace (L : Set G) :=
  isCompact_iff_compactSpace.mp L.isCompact

private theorem exists_bound_on_fixed_support (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (K : Compacts M)
    (hK : (K : Set M) ⊆ invertibleDomain r) (L : Compacts G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓓_{K}(M, ℂ)) (g : (L : Set G)),
      ‖borelAverage μ weight (TestFunction.ofSupportedIn hK f) g.val.val‖ ≤
        C * ‖(f : M →ᵇ ℂ)‖ := by
  let P : Set G := Units.val ⁻¹' (K : Set M)
  have hP : IsCompact P := RealGodement.isCompact_val_preimage K.isCompact (fun _ h => hK h)
  let S : Set B := Subtype.val ⁻¹' (P * (L : Set G)⁻¹)
  have hclosed := isClosed_upperTriangularSubgroup (r + 1) ℝ
  have hS : IsCompact S := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (hP.mul L.isCompact.inv)
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn hweight.continuousOn
  refine ⟨max A 0 * μ.real S, mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg, ?_⟩
  intro f g
  have he : borelAverage μ weight (TestFunction.ofSupportedIn hK f) g.val.val =
      ∫ b in S, weight b * f (b.val.val * g.val.val) ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro b hb
    change weight b * f (b.val.val * g.val.val) = 0
    have hz : b.val.val * g.val.val ∉ K := by
      intro h
      exact hb ⟨b.val * g.val, h, g.val⁻¹, Set.mem_inv.mpr g.property,
        mul_inv_cancel_right b.val g.val⟩
    rw [show f (b.val.val * g.val.val) = 0 from f.zero_on_compl hz, mul_zero]
  have : IsFiniteMeasure (μ.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hS.measure_lt_top⟩
  have hbd : ∀ᵐ b ∂μ.restrict S,
      ‖weight b * f (b.val.val * g.val.val)‖ ≤ max A 0 * ‖(f : M →ᵇ ℂ)‖ :=
    ae_restrict_of_forall_mem hS.measurableSet fun b hb => by
      rw [norm_mul]
      exact mul_le_mul ((hA b hb).trans (le_max_left _ _))
        ((f : M →ᵇ ℂ).norm_coe_le_norm _) (norm_nonneg _) (le_max_right _ _)
  rw [he]
  have h := norm_integral_le_of_norm_le_const hbd
  simpa only [Measure.real, Measure.restrict_apply_univ, mul_right_comm (max A 0)] using h

private def averageOnCompact (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (L : Compacts G) (f : Test) :
    C((L : Set G), ℂ) :=
  ⟨fun g => borelAverage μ weight f g.val.val,
    (contDiffOn_borelAverage μ hweight f).continuousOn.comp_continuous
      (Units.continuous_val.comp continuous_subtype_val) fun g => ⟨g.val, rfl⟩⟩

private def fixedSupportAverageCLM (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (L : Compacts G) (K : Compacts M)
    (hK : (K : Set M) ⊆ invertibleDomain r) :
    𝓓_{K}(M, ℂ) →L[ℂ] C((L : Set G), ℂ) := by
  let I : 𝓓_{K}(M, ℂ) →L[ℂ] Test := TestFunction.ofSupportedInCLM ℂ hK
  let F : 𝓓_{K}(M, ℂ) →ₗ[ℂ] C((L : Set G), ℂ) :=
    { toFun := fun f => averageOnCompact μ hweight L (I f)
      map_add' := by
        intro f h
        ext g
        change borelAverage μ weight (I (f + h)) g.val.val =
          borelAverage μ weight (I f) g.val.val + borelAverage μ weight (I h) g.val.val
        rw [map_add]
        exact borelAverage_add μ hweight _ _ g.val.val
      map_smul' := by
        intro c f
        ext g
        change borelAverage μ weight (I (c • f)) g.val.val =
          c * borelAverage μ weight (I f) g.val.val
        rw [map_smul]
        exact borelAverage_smul μ weight c _ g.val.val }
  refine ⟨F, continuous_of_continuousAt_zero F (Metric.continuousAt_iff'.mpr fun ε hε => ?_)⟩
  obtain ⟨C, hC, hbd⟩ := exists_bound_on_fixed_support μ hweight K hK L
  let P : 𝓓_{K}(M, ℂ) →L[ℂ] M →ᵇ ℂ := ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℂ
  have h := ((continuous_const.mul P.continuous.norm).continuousAt.eventually_lt
    continuousAt_const (by simpa using hε : C * ‖P 0‖ < ε))
  filter_upwards [h] with f hf
  rw [map_zero F, dist_zero_right]
  apply lt_of_le_of_lt _ hf
  exact (ContinuousMap.norm_le (F f) (mul_nonneg hC (norm_nonneg _))).mpr (hbd f)

/-- Borel averaging is continuous for the supremum on each compact output set. -/
def averageOnCompactCLM (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (L : Compacts G) :
    Test →L[ℂ] C((L : Set G), ℂ) :=
  TestFunction.limitCLM ℂ (averageOnCompact μ hweight L)
    (fixedSupportAverageCLM μ hweight L) (fun _ _ _ => rfl)

@[simp]
theorem averageOnCompactCLM_apply (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (L : Compacts G) (f : Test) (g : (L : Set G)) :
    averageOnCompactCLM μ hweight L f g = borelAverage μ weight f g.val.val := rfl

private def fixedSupportRightDerivativeCLM (Y : M) (K : Compacts M) :
    𝓓_{K}(M, ℂ) →L[ℝ] 𝓓_{K}(M, ℂ) :=
  (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ (E := M)).flip
    (LinearMap.mulRight ℝ Y).toContinuousLinearMap.contDiff).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

/-- The matrix right derivative acts continuously on each test space. -/
def rightDerivativeTestCLM (Y : M) : Test →L[ℝ] Test :=
  TestFunction.limitCLM ℝ (rightDerivativeTest Y)
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ hK).comp (fixedSupportRightDerivativeCLM Y K))
    (fun K hK f => by
      ext X
      change fderiv ℝ f X (X * Y) =
        (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f) X (X * Y)
      rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f (by simp)])

@[simp]
theorem rightDerivativeTestCLM_apply (Y : M) (f : Test) :
    rightDerivativeTestCLM Y f = rightDerivativeTest Y f := rfl

/-- Iterated right differentiation on the test space, in the order of the given word. -/
def rightDerivativeWordTestCLM (Xs : List M) : Test →L[ℝ] Test :=
  Xs.foldr (fun X A => (rightDerivativeTestCLM X).comp A) (ContinuousLinearMap.id ℝ Test)

theorem contMDiff_borelAverage (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (f : Test) :
    ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (fun g : G => borelAverage μ weight f g.val) :=
  contMDiff_of_contDiffOn (contDiffOn_borelAverage μ hweight f) (fun _ => rfl)

private theorem rightDerivative_average (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (f : Test) (Y : M) (g : G) :
    rightDerivative (matrixModel ℝ (r + 1)) Y (fun u : G => borelAverage μ weight f u.val) g =
      borelAverage μ weight (rightDerivativeTest Y f) g.val := by
  rw [rightDerivative_eq_fderiv (contMDiff_borelAverage μ hweight f)]
  have he : unitsExtension (fun u : G => borelAverage μ weight f u.val) =ᶠ[𝓝 g.val]
      borelAverage μ weight f := by
    have hg : g.val ∈ invertibleDomain r := ⟨g, rfl⟩
    filter_upwards [(invertibleDomain r).isOpen.mem_nhds hg] with X hX
    obtain ⟨u, rfl⟩ := hX
    exact unitsExtension_val _ u
  rw [he.fderiv_eq]
  exact fderiv_borelAverage_mul_right μ hweight f ⟨g, rfl⟩ Y

/-- Every group right-derivative word of an average is the average of the
same word on the matrix test. -/
theorem iteratedRightDerivative_borelAverage (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
    {weight : B → ℂ} (hweight : Continuous weight) (Xs : List M) (f : Test) (g : G) :
    RealLocalWhittaker.iteratedRightDerivative r Xs (fun u : G => borelAverage μ weight f u.val) g =
      borelAverage μ weight (rightDerivativeWordTestCLM Xs f) g.val := by
  induction Xs generalizing g with
  | nil => rfl
  | cons Y Xs ih =>
    change rightDerivative (matrixModel ℝ (r + 1)) Y
        (RealLocalWhittaker.iteratedRightDerivative r Xs (fun u : G => borelAverage μ weight f u.val)) g =
      borelAverage μ weight (rightDerivativeTest Y (rightDerivativeWordTestCLM Xs f)) g.val
    rw [funext ih]
    exact rightDerivative_average μ hweight _ Y g

/-- All compact right-derivative coordinates of the upper triangular average
come from continuous linear maps on the test space. -/
def RealBorelAverageContinuityStatement : Prop :=
  ∀ (r : ℕ) (μ : Measure (upperTriangularSubgroup (r + 1) ℝ)) [IsFiniteMeasureOnCompacts μ]
    (weight : upperTriangularSubgroup (r + 1) ℝ → ℂ), Continuous weight →
    ∀ (L : Compacts (Langlands.GeneralLinear (r + 1) ℝ))
      (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)),
      ∃ A : 𝓓(invertibleDomain r, ℂ) →L[ℝ] C((L : Set (Langlands.GeneralLinear (r + 1) ℝ)), ℂ),
        ∀ (f : 𝓓(invertibleDomain r, ℂ)) (g : (L : Set (Langlands.GeneralLinear (r + 1) ℝ))),
          A f g = RealLocalWhittaker.iteratedRightDerivative r Xs
            (fun u => borelAverage μ weight f u.val) g.val

theorem realBorelAverageContinuity : RealBorelAverageContinuityStatement := by
  intro r μ _ weight hweight L Xs
  refine ⟨((averageOnCompactCLM μ hweight L).restrictScalars ℝ).comp (rightDerivativeWordTestCLM Xs),
    fun f g => ?_⟩
  exact (iteratedRightDerivative_borelAverage μ hweight Xs f g.val).symm

end Langlands.Global.RankinSelbergGlobal.RealBorelAverageContinuity
