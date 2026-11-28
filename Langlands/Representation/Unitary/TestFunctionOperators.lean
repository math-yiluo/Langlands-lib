import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Integrated operators of test functions

For a jointly continuous representation `ρ` of a second countable locally compact group `G` on a
complex Banach space and a bounded measurable compactly supported function `φ` (a *test
function*), the operator `ρ(φ) v = ∫ φ(g) ρ(g) v dμ(g)` is bounded. This module constructs it and
proves the facts used for the irreducible tempered component theorem: left translation,
intertwining, invariance of closed invariant subspaces, approximate identities, and the norm
continuity of `g ↦ ρ(g) ρ(φ)` for isometric `ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.TemperedComponent

open Langlands.Archimedean

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- A test function: measurable, bounded and compactly supported. -/
def IsTestFunction (φ : G → ℂ) : Prop :=
  Measurable φ ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ HasCompactSupport φ

variable {μ : Measure G} [μ.IsHaarMeasure]

theorem IsTestFunction.integrable {φ : G → ℂ} (hφ : IsTestFunction φ) : Integrable φ μ := by
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hφ
  refine (integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)).mp ?_
  exact Measure.integrableOn_of_bounded (M := C) hc.isCompact.measure_lt_top.ne
    hm.aestronglyMeasurable (Eventually.of_forall hC)

theorem IsTestFunction.comp_mul_left {φ : G → ℂ} (hφ : IsTestFunction φ) (p : G) :
    IsTestFunction fun g => φ (p * g) := by
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hφ
  exact ⟨hm.comp (measurable_const_mul p), ⟨C, fun g => hC _⟩,
    hc.comp_homeomorph (Homeomorph.mulLeft p)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem continuous_orbit {ρ : G →* (E →L[ℂ] E)} (hρ : IsContinuousRepresentation ρ) (v : E) :
    Continuous fun g => ρ g v :=
  hρ.comp (continuous_id.prodMk continuous_const)

/-- A jointly continuous representation is uniformly bounded on compact sets. -/
theorem exists_opNorm_le_of_isCompact {ρ : G →* (E →L[ℂ] E)} (hρ : IsContinuousRepresentation ρ)
    {S : Set G} (hS : IsCompact S) : ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ S, ‖ρ g‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun g : S => ρ g) fun x => by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_orbit hρ x).continuousOn
    exact ⟨C, fun g => hC g g.2⟩
  exact ⟨max C 0, le_max_right _ _, fun g hg => (hC ⟨g, hg⟩).trans (le_max_left _ _)⟩

theorem integrable_smul_orbit {ρ : G →* (E →L[ℂ] E)} (hρ : IsContinuousRepresentation ρ)
    {φ : G → ℂ} (hφ : IsTestFunction φ) (v : E) :
    Integrable (fun g => φ g • ρ g v) μ := by
  obtain ⟨M, -, hM⟩ := exists_opNorm_le_of_isCompact hρ hφ.2.2.isCompact
  refine (hφ.integrable.norm.mul_const (M * ‖v‖)).mono'
    (hφ.1.aestronglyMeasurable.smul (continuous_orbit hρ v).aestronglyMeasurable)
    (Eventually.of_forall fun g => ?_)
  rw [norm_smul]
  by_cases hg : g ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_left (((ρ g).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hM g hg) (norm_nonneg _))) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hg]

/-- The integrated operator `ρ(φ) v = ∫ φ(g) ρ(g) v dμ(g)` of a test function. -/
def testOp (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : IsContinuousRepresentation ρ) (φ : G → ℂ) (hφ : IsTestFunction φ) : E →L[ℂ] E :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun v => ∫ g, φ g • ρ g v ∂μ
      map_add' := fun v w => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_smul_orbit hρ hφ v) (integrable_smul_orbit hρ hφ w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply, smul_comm (φ _) c]
        exact integral_smul c _ }
    (by
      obtain ⟨M, hM0, hM⟩ := exists_opNorm_le_of_isCompact hρ hφ.2.2.isCompact
      refine ⟨(∫ g, ‖φ g‖ ∂μ) * M, fun v => ?_⟩
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ g, φ g • ρ g v ∂μ‖ ≤ ∫ g, ‖φ g‖ * (M * ‖v‖) ∂μ := by
            refine norm_integral_le_of_norm_le (hφ.integrable.norm.mul_const _)
              (Eventually.of_forall fun g => ?_)
            rw [norm_smul]
            by_cases hg : g ∈ tsupport φ
            · exact mul_le_mul_of_nonneg_left (((ρ g).le_opNorm v).trans
                (mul_le_mul_of_nonneg_right (hM g hg) (norm_nonneg _))) (norm_nonneg _)
            · simp [image_eq_zero_of_notMem_tsupport hg]
        _ = (∫ g, ‖φ g‖ ∂μ) * M * ‖v‖ := by rw [integral_mul_const]; ring)

@[simp]
theorem testOp_apply (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ) (φ : G → ℂ)
    (hφ : IsTestFunction φ) (v : E) : testOp μ ρ hρ φ hφ v = ∫ g, φ g • ρ g v ∂μ := rfl

/-- For a norm-preserving representation, `ρ(φ₁) - ρ(φ₂)` is bounded by `‖φ₁ - φ₂‖₁`. -/
theorem norm_testOp_sub_le (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ)
    (hρn : ∀ g v, ‖ρ g v‖ = ‖v‖) (φ₁ φ₂ : G → ℂ) (h₁ : IsTestFunction φ₁)
    (h₂ : IsTestFunction φ₂) :
    ‖testOp μ ρ hρ φ₁ h₁ - testOp μ ρ hρ φ₂ h₂‖ ≤ ∫ g, ‖φ₁ g - φ₂ g‖ ∂μ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
    fun v => ?_
  rw [sub_apply, testOp_apply, testOp_apply,
    ← integral_sub (integrable_smul_orbit hρ h₁ v) (integrable_smul_orbit hρ h₂ v)]
  calc ‖∫ g, (φ₁ g • ρ g v - φ₂ g • ρ g v) ∂μ‖ ≤ ∫ g, ‖φ₁ g - φ₂ g‖ * ‖v‖ ∂μ := by
        refine norm_integral_le_of_norm_le ((h₁.integrable.sub h₂.integrable).norm.mul_const _)
          (Eventually.of_forall fun g => ?_)
        rw [← sub_smul, norm_smul, hρn]
    _ = (∫ g, ‖φ₁ g - φ₂ g‖ ∂μ) * ‖v‖ := integral_mul_const _ _

theorem norm_testOp_le (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ)
    (hρn : ∀ g v, ‖ρ g v‖ = ‖v‖) (φ : G → ℂ) (hφ : IsTestFunction φ) :
    ‖testOp μ ρ hρ φ hφ‖ ≤ ∫ g, ‖φ g‖ ∂μ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
    fun v => ?_
  rw [testOp_apply]
  calc ‖∫ g, φ g • ρ g v ∂μ‖ ≤ ∫ g, ‖φ g‖ * ‖v‖ ∂μ :=
        norm_integral_le_of_norm_le (hφ.integrable.norm.mul_const _)
          (Eventually.of_forall fun g => by rw [norm_smul, hρn])
    _ = (∫ g, ‖φ g‖ ∂μ) * ‖v‖ := integral_mul_const _ _

/-- Left translation: `ρ(p) ρ(φ) = ρ(φ(p⁻¹ ·))`. -/
theorem comp_testOp (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ) (φ : G → ℂ)
    (hφ : IsTestFunction φ) (p : G) :
    (ρ p).comp (testOp μ ρ hρ φ hφ) =
      testOp μ ρ hρ (fun g => φ (p⁻¹ * g)) (hφ.comp_mul_left p⁻¹) := by
  ext v
  rw [ContinuousLinearMap.comp_apply, testOp_apply, testOp_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_orbit hρ hφ v)]
  rw [← integral_mul_left_eq_self (fun g => φ (p⁻¹ * g) • ρ g v) p]
  simp only [map_smul, inv_mul_cancel_left, map_mul, mul_apply_eq_comp]

/-- An intertwiner commutes with the integrated operators. -/
theorem intertwiner_comp_testOp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ)
    (ρ' : G →* (F →L[ℂ] F)) (hρ' : IsContinuousRepresentation ρ') (j : E →L[ℂ] F)
    (hj : ∀ g x, j (ρ g x) = ρ' g (j x)) (φ : G → ℂ) (hφ : IsTestFunction φ) :
    j.comp (testOp μ ρ hρ φ hφ) = (testOp μ ρ' hρ' φ hφ).comp j := by
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, testOp_apply, testOp_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_smul_orbit hρ hφ v)]
  simp only [map_smul, hj]

/-- The Bochner integral of `φ • f` with `f` continuous with values in a closed submodule lies in
the submodule. -/
theorem integral_smul_mem_of_continuous (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    {φ : G → ℂ} (hφ : Measurable φ) {f : G → E} (hf : Continuous f) (hfS : ∀ g, f g ∈ S)
    (hint : Integrable (fun g => φ g • f g) μ) : ∫ g, φ g • f g ∂μ ∈ S := by
  have : CompleteSpace S := hS.completeSpace_coe
  let f' : G → S := fun g => ⟨f g, hfS g⟩
  have hf' : Continuous f' := hf.subtype_mk hfS
  have hint' : Integrable (fun g => φ g • f' g) μ := by
    refine hint.norm.mono' (hφ.aestronglyMeasurable.smul hf'.aestronglyMeasurable)
      (Eventually.of_forall fun g => ?_)
    rw [norm_smul, norm_smul]
    rfl
  have h := ContinuousLinearMap.integral_comp_comm S.subtypeL hint'
  have heq : (fun g => S.subtypeL (φ g • f' g)) = fun g => φ g • f g := by
    funext g; rfl
  rw [heq] at h
  rw [h]
  exact (∫ g, φ g • f' g ∂μ).2

/-- A closed invariant submodule is invariant under the integrated operators. -/
theorem testOp_mem (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ) (φ : G → ℂ)
    (hφ : IsTestFunction φ) (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (hSinv : ∀ g, ∀ v ∈ S, ρ g v ∈ S) {v : E} (hv : v ∈ S) : testOp μ ρ hρ φ hφ v ∈ S :=
  integral_smul_mem_of_continuous S hS hφ.1 (continuous_orbit hρ v) (fun g => hSinv g v hv)
    (integrable_smul_orbit hρ hφ v)

/-! ### Approximate identities -/

/-- A sequence of nonnegative test functions of integral one whose supports shrink to the
identity. -/
structure IsApproxIdentity (μ : Measure G) (χ : ℕ → G → ℂ) : Prop where
  test : ∀ n, IsTestFunction (χ n)
  real_nonneg : ∀ n g, χ n g = (‖χ n g‖ : ℂ)
  integral_eq_one : ∀ n, ∫ g, χ n g ∂μ = 1
  support_subset : ∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop, Function.support (χ n) ⊆ U

theorem IsApproxIdentity.integral_norm {χ : ℕ → G → ℂ} (hχ : IsApproxIdentity μ χ) (n : ℕ) :
    ∫ g, ‖χ n g‖ ∂μ = 1 := by
  have h := hχ.integral_eq_one n
  have h2 : ∫ g, χ n g ∂μ = ((∫ g, ‖χ n g‖ ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun g => hχ.real_nonneg n g)
  rw [h2] at h
  exact_mod_cast h

theorem IsApproxIdentity.tendsto {χ : ℕ → G → ℂ} (hχ : IsApproxIdentity μ χ)
    (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ) (v : E) :
    Tendsto (fun n => testOp μ ρ hρ (χ n) (hχ.test n) v) atTop (𝓝 v) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hU : {g : G | dist (ρ g v) v < ε / 2} ∈ 𝓝 (1 : G) := by
    have hc : Tendsto (fun g => ρ g v) (𝓝 1) (𝓝 v) := by
      simpa using (continuous_orbit hρ v).tendsto 1
    exact hc (Metric.ball_mem_nhds v (half_pos hε))
  obtain ⟨N, hN⟩ := (hχ.support_subset _ hU).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have hsupp := hN n hn
  have hv : ∫ g, χ n g • ρ g v ∂μ - v = ∫ g, (χ n g • ρ g v - χ n g • v) ∂μ := by
    rw [integral_sub (integrable_smul_orbit hρ (hχ.test n) v)
      ((hχ.test n).integrable.smul_const v), integral_smul_const, hχ.integral_eq_one, one_smul]
  rw [dist_eq_norm, testOp_apply, hv]
  calc ‖∫ g, (χ n g • ρ g v - χ n g • v) ∂μ‖ ≤ ∫ g, ‖χ n g‖ * (ε / 2) ∂μ := by
        refine norm_integral_le_of_norm_le ((hχ.test n).integrable.norm.mul_const _)
          (Eventually.of_forall fun g => ?_)
        rw [← smul_sub, norm_smul]
        by_cases hg : χ n g = 0
        · simp [hg]
        · exact mul_le_mul_of_nonneg_left
            (by have h := hsupp hg; rw [Set.mem_ofPred_eq, dist_eq_norm] at h; exact h.le)
            (norm_nonneg _)
    _ = ε / 2 := by rw [integral_mul_const, hχ.integral_norm, one_mul]
    _ < ε := half_lt_self hε

omit [μ.IsHaarMeasure] in
theorem exists_approxIdentity (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ χ : ℕ → G → ℂ, IsApproxIdentity μ χ := by
  obtain ⟨x, hx⟩ := (𝓝 (1 : G)).exists_antitone_basis
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : G)
  let U : ℕ → Set G := fun n => interior (x n ∩ K)
  have hUo : ∀ n, IsOpen (U n) := fun n => isOpen_interior
  have hU1 : ∀ n, (1 : G) ∈ U n := fun n =>
    mem_interior_iff_mem_nhds.mpr (inter_mem (hx.mem n) hKn)
  have hUK : ∀ n, U n ⊆ K := fun n => interior_subset.trans Set.inter_subset_right
  have hUpos : ∀ n, 0 < μ (U n) := fun n => (hUo n).measure_pos μ ⟨1, hU1 n⟩
  have hUfin : ∀ n, μ (U n) < ⊤ := fun n => (measure_mono (hUK n)).trans_lt hK.measure_lt_top
  let c : ℕ → ℝ := fun n => (μ.real (U n))⁻¹
  have hreal_pos : ∀ n, 0 < μ.real (U n) := fun n =>
    ENNReal.toReal_pos (hUpos n).ne' (hUfin n).ne
  let χ : ℕ → G → ℂ := fun n => (U n).indicator fun _ => ((c n : ℝ) : ℂ)
  refine ⟨χ, ⟨fun n => ?_, fun n g => ?_, fun n => ?_, fun V hV => ?_⟩⟩
  · refine ⟨measurable_const.indicator (hUo n).measurableSet, ⟨|c n|, fun g => ?_⟩, ?_⟩
    · by_cases hg : g ∈ U n
      · simp [χ, hg]
      · simp [χ, hg]
    · refine HasCompactSupport.intro hK fun g hg => ?_
      exact Set.indicator_of_notMem (fun h => hg (hUK n h)) _
  · by_cases hg : g ∈ U n
    · simp only [χ, Set.indicator_of_mem hg, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr (hreal_pos n))]
    · simp [χ, hg]
  · rw [integral_indicator_const _ (hUo n).measurableSet]
    simp only [c, Complex.real_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hreal_pos n).ne', Complex.ofReal_one]
  · rw [hx.mem_iff] at hV
    obtain ⟨N, hN⟩ := hV
    refine eventually_atTop.mpr ⟨N, fun n hn g hg => ?_⟩
    have hgU : g ∈ U n := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    exact hx.antitone hn (interior_subset hgU).1 |> fun h => hN h

/-! ### Norm continuity of left translates -/

/-- Left translation is continuous on `L¹(G)`. -/
theorem tendsto_integral_norm_translate_sub {φ : G → ℂ} (hφ : Integrable φ μ) (g₀ : G) :
    Tendsto (fun g => ∫ x, ‖φ (g⁻¹ * x) - φ (g₀⁻¹ * x)‖ ∂μ) (𝓝 g₀) (𝓝 0) := by
  have : Fact ((1 : ENNReal) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  have hm : MemLp φ 1 μ := memLp_one_iff_integrable.mpr hφ
  let A : G → Lp ℂ 1 μ := fun g => DomMulAct.mk g⁻¹ • hm.toLp φ
  have hA : Continuous A := (DomMulAct.continuous_mk.comp continuous_inv).smul continuous_const
  have hAg : ∀ g, (A g : G → ℂ) =ᵐ[μ] fun x => φ (g⁻¹ * x) := fun g => by
    rw [show A g = _ from DomMulAct.mk_smul_toLp g⁻¹ hm]
    exact MemLp.coeFn_toLp _
  have hnorm : ∀ g, ‖A g - A g₀‖ = ∫ x, ‖φ (g⁻¹ * x) - φ (g₀⁻¹ * x)‖ ∂μ := by
    intro g
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (A g) (A g₀), hAg g, hAg g₀] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have h := hA.tendsto g₀
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [hnorm] using h

/-- For a norm-preserving representation, `g ↦ ρ(g) ρ(φ)` is continuous in operator norm. -/
theorem continuous_comp_testOp (ρ : G →* (E →L[ℂ] E)) (hρ : IsContinuousRepresentation ρ)
    (hρn : ∀ g v, ‖ρ g v‖ = ‖v‖) (φ : G → ℂ) (hφ : IsTestFunction φ) :
    Continuous fun g => (ρ g).comp (testOp μ ρ hρ φ hφ) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_)
    (tendsto_integral_norm_translate_sub (μ := μ) hφ.integrable g₀)
  rw [comp_testOp, comp_testOp]
  exact norm_testOp_sub_le (μ := μ) ρ hρ hρn _ _ _ _

end Langlands.Analysis.TemperedComponent
