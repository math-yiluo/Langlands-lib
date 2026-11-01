import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox
import Langlands.Representation.RankinSelberg.RankOneMatrixUnfolding
import Langlands.Representation.GodementJacquet.LeftAveraging
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Right principal averaging and uniform original-integral extraction -/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg

universe uG uF

section RightAverage

variable {G : Type uG} [Group G] [MeasurableSpace G]

/-- Right averaging normalized by the mass of its integration set. -/
def normalizedRightAverage (μ : Measure G) (Ω : Set G) (H : G → ℂ) : G → ℂ :=
  fun g => (μ.real Ω : ℂ)⁻¹ * ∫ k in Ω, H (g * k) ∂μ

variable [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]

omit [MeasurableInv G] in
/-- Right averaging preserves convergence under a right invariant weight,
and multiplies the unnormalized integral by the averaging mass. -/
theorem rightAverage_integral (Ω : Set G) (hΩm : MeasurableSet Ω) (hΩfin : μ Ω ≠ ⊤)
    (a H : G → ℂ) (ha : ∀ k ∈ Ω, ∀ g, a (g * k) = a g)
    (hconv : Integrable (fun g => a g * H g) μ) :
    Integrable (fun g => a g * ∫ k in Ω, H (g * k) ∂μ) μ ∧
      ∫ g, a g * (∫ k in Ω, H (g * k) ∂μ) ∂μ =
        (μ.real Ω : ℂ) * ∫ g, a g * H g ∂μ := by
  let ν := μ.restrict Ω
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hΩfin
  have hs : MeasurePreserving (fun z : G × G => (z.1, z.2 * z.1))
      (ν.prod μ) (ν.prod μ) := measurePreserving_prod_mul_right ν μ
  let Q : G × G → ℂ := fun z => a (z.2 * z.1⁻¹) * H z.2
  let P : G × G → ℂ := fun z => (1 : ℂ) * (a z.2 * H z.2)
  have hP : Integrable P (ν.prod μ) := (integrable_const (1 : ℂ)).mul_prod hconv
  have hae : ∀ᵐ z ∂(ν.prod μ), z.1 ∈ Ω :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hΩm)
  have hPQ : P =ᵐ[ν.prod μ] Q := by
    filter_upwards [hae] with z hz
    have h := ha z.1 hz (z.2 * z.1⁻¹)
    rw [inv_mul_cancel_right] at h
    simp only [P, Q, one_mul, h]
  have hQ : Integrable Q (ν.prod μ) := hP.congr hPQ
  let R : G × G → ℂ := fun z => a z.2 * H (z.2 * z.1)
  have hR_eq : R = Q ∘ (fun z : G × G => (z.1, z.2 * z.1)) := by
    funext z
    simp only [R, Q, Function.comp_apply, mul_inv_cancel_right]
  have hR : Integrable R (ν.prod μ) := by
    rw [hR_eq]
    exact hs.integrable_comp_of_integrable hQ
  have hpoint : (fun g => a g * ∫ k in Ω, H (g * k) ∂μ) =
      fun g => ∫ k, R (k, g) ∂ν := by
    funext g
    simp only [R, ν]
    rw [integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hpoint]
    exact hR.integral_prod_right
  · calc
      ∫ g, a g * (∫ k in Ω, H (g * k) ∂μ) ∂μ =
          ∫ g, ∫ k, R (k, g) ∂ν ∂μ := by rw [hpoint]
      _ = ∫ z, R z ∂(ν.prod μ) := (integral_prod_symm R hR).symm
      _ = ∫ z, Q z ∂(ν.prod μ) := by
        have hm : AEStronglyMeasurable Q
            (Measure.map (fun z : G × G => (z.1, z.2 * z.1)) (ν.prod μ)) := by
          rw [hs.map_eq]
          exact hQ.aestronglyMeasurable
        rw [hR_eq]
        simp only [Function.comp_apply]
        rw [← integral_map hs.measurable.aemeasurable hm, hs.map_eq]
      _ = ∫ z, P z ∂(ν.prod μ) := integral_congr_ae hPQ.symm
      _ = (∫ _k, (1 : ℂ) ∂ν) * ∫ g, a g * H g ∂μ :=
        integral_prod_mul (μ := ν) (ν := μ) (fun _ : G => (1 : ℂ)) (fun g => a g * H g)
      _ = (μ.real Ω : ℂ) * ∫ g, a g * H g ∂μ := by
        simp [ν, integral_const]

omit [MeasurableInv G] in
/-- Normalized right averaging preserves an actually convergent weighted integral. -/
theorem normalizedRightAverage_integral (Ω : Set G) (hΩm : MeasurableSet Ω)
    (hΩfin : μ Ω ≠ ⊤) (hΩpos : μ Ω ≠ 0)
    (a H : G → ℂ) (ha : ∀ k ∈ Ω, ∀ g, a (g * k) = a g)
    (hconv : Integrable (fun g => a g * H g) μ) :
    Integrable (fun g => a g * normalizedRightAverage μ Ω H g) μ ∧
      ∫ g, a g * normalizedRightAverage μ Ω H g ∂μ =
        ∫ g, a g * H g ∂μ := by
  have hmass : (μ.real Ω : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hΩpos, hΩfin⟩
  obtain ⟨hc, hv⟩ := rightAverage_integral μ Ω hΩm hΩfin a H ha hconv
  have hpoint : (fun g => a g * normalizedRightAverage μ Ω H g) =
      fun g => (μ.real Ω : ℂ)⁻¹ * (a g * ∫ k in Ω, H (g * k) ∂μ) := by
    funext g
    simp only [normalizedRightAverage]
    ring
  rw [hpoint]
  exact ⟨hc.const_mul _, by
    rw [integral_const_mul, hv, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]⟩

end RightAverage

section SubgroupAverage

variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant]

/-- Left Haar invariance in the integration parameter gives right subgroup
invariance of a right average, without assuming any convergence. -/
theorem normalizedRightAverage_mul_subgroup (K : Subgroup G)
    (hKm : MeasurableSet (K : Set G)) (H : G → ℂ) {k : G} (hk : k ∈ K) (g : G) :
    normalizedRightAverage μ K H (g * k) = normalizedRightAverage μ K H g := by
  have hpre : (fun x : G => k * x) ⁻¹' (K : Set G) = K := by
    ext x
    exact K.mul_mem_cancel_left hk
  have ht := (measurePreserving_mul_left μ k).restrict_preimage hKm
  rw [hpre] at ht
  have hi := ht.integral_comp (measurableEmbedding_mulLeft k) (fun x => H (g * x))
  simp only [normalizedRightAverage]
  congr 1
  simpa only [mul_assoc] using hi

/-- Averaging a right fixed function returns that same function. -/
theorem normalizedRightAverage_eq_of_fixed {G : Type uG} [Group G] [MeasurableSpace G]
    (μ : Measure G) (K : Set G) (hKm : MeasurableSet K)
    (hKfin : μ K ≠ ⊤) (hKpos : μ K ≠ 0)
    (H : G → ℂ) (hH : ∀ k ∈ K, ∀ g, H (g * k) = H g) :
    normalizedRightAverage μ K H = H := by
  have hm : (μ.real K : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hKpos, hKfin⟩
  funext g
  rw [normalizedRightAverage, setIntegral_congr_fun hKm (fun k hk => hH k hk g)]
  simp [integral_const, hm]

end SubgroupAverage

namespace RankOneBox

open GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa
open UnequalRankMirabolicUnitTest

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalAverageTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalAverageValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalAverageLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalAverageT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance principalAverageSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance principalAverageGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalAverageGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalAverageGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance principalAverageMatrixLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin n) (Fin n) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F.Carrier))
local instance principalAverageGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n F.Carrier) := inferInstance

variable {n : ℕ}

/-- The actual normalized right average over the principal subgroup. -/
def principalAverage (a : ℕ) (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) :
    Langlands.GeneralLinear (n + 1) F.Carrier → ℂ :=
  normalizedRightAverage (generalLinearHaar F.Carrier n)
    (principalLevelSubgroup F.Carrier n a) H

theorem continuous_principalAverage (a : ℕ)
    {H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hH : Continuous H) :
    Continuous (principalAverage F a H) := by
  change Continuous (fun g => _ * ∫ k in
    (principalLevelSubgroup F.Carrier n a : Set _), H (g * k) ∂generalLinearHaar F.Carrier n)
  apply Continuous.const_mul
  exact continuous_parametric_integral_of_continuous (f := fun g k => H (g * k))
    (hH.comp (continuous_fst.mul continuous_snd))
    (isCompact_principalLevelOpenSubgroup F.Carrier n a)

theorem principalAverage_mul (a : ℕ)
    (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ principalLevelSubgroup F.Carrier n a) (g) :
    principalAverage F a H (g * k) = principalAverage F a H g :=
  normalizedRightAverage_mul_subgroup _ _ (principalLevelOpenSubgroup F.Carrier n a).isOpen.measurableSet H hk g

theorem principalAverage_equivariant (ψ : UnitaryAdditiveCharacter F.Carrier) (a : ℕ)
    (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (heq : ∀ u : upperUnipotent (n + 1) F.Carrier, ∀ h,
      H (u.val * h) = (standardCharacter ψ n u : ℂ) * H h)
    (u : upperUnipotent (n + 1) F.Carrier) (g) :
    principalAverage F a H (u.val * g) =
      (standardCharacter ψ n u : ℂ) * principalAverage F a H g := by
  simp only [principalAverage, normalizedRightAverage, mul_assoc, heq, integral_const_mul]
  ring

/-- The same fixed box is right invariant on the entire matrix space. -/
theorem uniformBox_mul_principalLevel (q : ℤ) (a : ℕ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ principalLevelSubgroup F.Carrier n a) :
    boxLatticeTest F (q + a) q a (X * k.val) = boxLatticeTest F (q + a) q a X := by
  have hb := mul_mem_box_iff_of_le F (show q ≤ q + a by omega)
    (fun _ hy => principalLevel_firstRow F q a hy) X hk
  simp only [boxLatticeTest_apply]
  by_cases hX : X ∈ box F (q + a) q a <;> simp [hb, hX]

/-- Any convergent original box integral is preserved by principal averaging. -/
theorem principalAverage_box_integral (q : ℤ) (a : ℕ)
    (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hconv : Integrable (fun g => boxLatticeTest F (q + a) q a g.val * H g)
      (generalLinearHaar F.Carrier n)) :
    Integrable (fun g => boxLatticeTest F (q + a) q a g.val * principalAverage F a H g)
      (generalLinearHaar F.Carrier n) ∧
    ∫ g, boxLatticeTest F (q + a) q a g.val * principalAverage F a H g
      ∂generalLinearHaar F.Carrier n =
        ∫ g, boxLatticeTest F (q + a) q a g.val * H g
          ∂generalLinearHaar F.Carrier n := by
  let K := principalLevelOpenSubgroup F.Carrier n a
  exact normalizedRightAverage_integral (generalLinearHaar F.Carrier n)
    (K : Set _) K.isOpen.measurableSet
    (isCompact_principalLevelOpenSubgroup F.Carrier n a).measure_lt_top.ne
    (K.isOpen.measure_pos (generalLinearHaar F.Carrier n) ⟨1, K.one_mem⟩).ne'
    (fun g => boxLatticeTest F (q + a) q a g.val) H
    (fun k hk g => uniformBox_mul_principalLevel F q a g.val hk) hconv

/-- One fixed box and right averaging extract every continuous equivariant H.
Only the original-to-averaged direction of convergence is asserted. -/
theorem principalAverage_extraction (ψ : UnitaryAdditiveCharacter F.Carrier)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    (H : Langlands.GeneralLinear (m + 1 + 1) F.Carrier → ℂ) (hH : Continuous H)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F.Carrier, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hconv : Integrable (fun h =>
      boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a h.val * H h)
      (generalLinearHaar F.Carrier (m + 1))) :
    Integrable (fun g => principalAverage F a H (rankOneEmbedding m g))
      (glOneMeasure F (m + 1)) ∧
    ∫ h, boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a h.val * H h
        ∂generalLinearHaar F.Carrier (m + 1) =
      (boxExtractionConstant F (n := m + 1)
        (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a : ℂ) *
        ∫ g, principalAverage F a H (rankOneEmbedding m g) ∂glOneMeasure F (m + 1) := by
  obtain ⟨hc, hv⟩ := principalAverage_box_integral F _ a H hconv
  obtain ⟨hiff, he⟩ := uniform_box_extraction F ψ ha hA (principalAverage F a H)
    (continuous_principalAverage F a hH)
    (principalAverage_equivariant F ψ a H heq) (fun _ hk g => principalAverage_mul F a H hk g)
  exact ⟨hiff.1 hc, hv.symm.trans he⟩

/-- The principal subgroup has finite, strictly positive Haar mass. -/
theorem principalLevel_mass_pos (a : ℕ) :
    0 < (generalLinearHaar F.Carrier n).real
      (principalLevelSubgroup F.Carrier n a : Set _) := by
  apply ENNReal.toReal_pos
  · exact ((principalLevelOpenSubgroup F.Carrier n a).isOpen.measure_pos _
      ⟨1, (principalLevelSubgroup F.Carrier n a).one_mem⟩).ne'
  · exact (isCompact_principalLevelOpenSubgroup F.Carrier n a).measure_lt_top.ne

/-- A positive scalar multiple of normalized Haar on the actual principal
subgroup. Its total mass is C rather than one. -/
def principalAveragingMeasure (a : ℕ) (C : ℝ) :
    Measure (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  ENNReal.ofReal (C / (generalLinearHaar F.Carrier n).real
    (principalLevelSubgroup F.Carrier n a : Set _)) •
      (generalLinearHaar F.Carrier n).restrict (principalLevelSubgroup F.Carrier n a)

instance principalAveragingMeasure_finite (a : ℕ) (C : ℝ) :
    IsFiniteMeasure (principalAveragingMeasure F (n := n) a C) := by
  have : IsFiniteMeasure ((generalLinearHaar F.Carrier n).restrict
      (principalLevelSubgroup F.Carrier n a : Set _)) :=
    isFiniteMeasure_restrict.mpr
      (isCompact_principalLevelOpenSubgroup F.Carrier n a).measure_lt_top.ne
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem principalAveragingMeasure_ae_mem (a : ℕ) (C : ℝ) :
    ∀ᵐ k ∂principalAveragingMeasure F (n := n) a C,
      k ∈ principalLevelSubgroup F.Carrier n a :=
  Measure.ae_smul_measure
    (ae_restrict_mem (principalLevelOpenSubgroup F.Carrier n a).isOpen.measurableSet) _

theorem principalAveragingMeasure_ae_det_norm (a : ℕ) (C : ℝ) :
    ∀ᵐ k ∂principalAveragingMeasure F (n := n) a C,
      normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1 := by
  filter_upwards [principalAveragingMeasure_ae_mem F a C] with k hk
  exact abv_det_eq_one F (principalLevel_le_integral F a hk)

theorem principalAveragingMeasure_integral (a : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (g) :
    ∫ k, H (g * k) ∂principalAveragingMeasure F a C =
      (C : ℂ) * principalAverage F a H g := by
  rw [principalAveragingMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (div_nonneg hC (principalLevel_mass_pos F a).le)]
  simp only [principalAverage, normalizedRightAverage, Complex.real_smul, Complex.ofReal_div]
  ring

theorem principalAveragingMeasure_mass (a : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    principalAveragingMeasure F (n := n) a C Set.univ = ENNReal.ofReal C := by
  have hp := principalLevel_mass_pos F (n := n) a
  have hf : generalLinearHaar F.Carrier n
      (principalLevelSubgroup F.Carrier n a : Set _) ≠ ⊤ :=
    (isCompact_principalLevelOpenSubgroup F.Carrier n a).measure_lt_top.ne
  simp only [principalAveragingMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  calc
    _ = ENNReal.ofReal (C / (generalLinearHaar F.Carrier n).real
        (principalLevelSubgroup F.Carrier n a : Set _)) *
        ENNReal.ofReal ((generalLinearHaar F.Carrier n).real
          (principalLevelSubgroup F.Carrier n a : Set _)) := by
      rw [measureReal_def, ENNReal.ofReal_toReal hf]
    _ = ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_mul (div_nonneg hC hp.le), div_mul_cancel₀ _ hp.ne']

theorem principalAveragingMeasure_integrable (a : ℕ) (C : ℝ)
    {H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hH : Continuous H) (g) :
    Integrable (fun k => H (g * k)) (principalAveragingMeasure F a C) := by
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  exact (hH.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact
    (isCompact_principalLevelOpenSubgroup F.Carrier n a)

/-- A principal fixed original function is multiplied by exactly C. -/
theorem principalAveragingMeasure_fixed (a : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (H : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hH : ∀ k ∈ principalLevelSubgroup F.Carrier n a, ∀ g, H (g * k) = H g)
    (g) :
    ∫ k, H (g * k) ∂principalAveragingMeasure F a C = (C : ℂ) * H g := by
  calc
    _ = ∫ _k, H g ∂principalAveragingMeasure F a C := by
      apply integral_congr_ae
      filter_upwards [principalAveragingMeasure_ae_mem F a C] with k hk
      exact hH k hk g
    _ = (C : ℂ) * H g := by
      simp [integral_const, measureReal_def, principalAveragingMeasure_mass F a hC,
        ENNReal.toReal_ofReal hC, Complex.real_smul]

/-- The fixed box extracts the actual compact principal measure average for
every continuous left equivariant function with convergent original integrand. -/
theorem principalMeasure_extraction (ψ : UnitaryAdditiveCharacter F.Carrier)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    (H : Langlands.GeneralLinear (m + 1 + 1) F.Carrier → ℂ) (hH : Continuous H)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F.Carrier, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hconv : Integrable (fun h =>
      boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a h.val * H h)
      (generalLinearHaar F.Carrier (m + 1))) :
    let C := boxExtractionConstant F (n := m + 1)
      (F.canonicalTopologicalData.additiveConductor ψ + a)
      (F.canonicalTopologicalData.additiveConductor ψ) a
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun g => ∫ k, H (rankOneEmbedding m g * k) ∂μ)
        (glOneMeasure F (m + 1)) ∧
      ∫ h, boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
          (F.canonicalTopologicalData.additiveConductor ψ) a h.val * H h
          ∂generalLinearHaar F.Carrier (m + 1) =
        ∫ g, ∫ k, H (rankOneEmbedding m g * k) ∂μ ∂glOneMeasure F (m + 1) := by
  dsimp only
  have hC := (boxExtractionConstant_pos F (n := m + 1)
    (q := F.canonicalTopologicalData.additiveConductor ψ) hA ha).le
  simp_rw [principalAveragingMeasure_integral F a hC]
  obtain ⟨hc, hv⟩ := principalAverage_extraction F ψ ha hA H hH heq hconv
  exact ⟨hc.const_mul _, by rw [integral_const_mul]; exact hv⟩

end RankOneBox

end Langlands.RankinSelberg
