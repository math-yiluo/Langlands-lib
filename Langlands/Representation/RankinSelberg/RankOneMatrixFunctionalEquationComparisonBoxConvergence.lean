import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxCoefficient
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof

/-! # Actual rank-one convergence from matrix analytic data

A deep box and a compact averaging subgroup preserve the actual model function
on the box. Tonelli's exact positive norm identity then transfers convergence
from the matrix coefficient to the rank-one integral.
-/

noncomputable section

namespace Langlands.RankinSelberg.RankOneBox

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa
open UnequalRankMirabolicUnitTest
open scoped NNReal ENNReal

universe uF uV

section Convergence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance boxConvergenceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance boxConvergenceValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance boxConvergenceLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance boxConvergenceT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance boxConvergenceMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance boxConvergenceBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local instance boxConvergenceUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance boxConvergenceUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance boxConvergenceSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance boxConvergenceUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance boxConvergenceUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance boxConvergenceUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- The explicit hypotheses needed by the rank-one box integral calculation. -/
def ModelBoxConditions (A q : ℤ) (a : ℕ) : Prop :=
  0 < a ∧ 0 ≤ A ∧ q ≤ 0 ∧
    (∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A)) ∧
    (∀ z ∈ 𝓛 q, ψ z = 1) ∧
    (∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 q) ∧
    (∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈ 𝓛 A)

/-- A compact averaging subgroup can be chosen so that its actual coefficient
agrees pointwise with the model function on a box satisfying all integral hypotheses. -/
theorem exists_box_averagedModelCoefficient_eq (hσ : IsSmooth σ) :
    ∃ (A q : ℤ) (a : ℕ), ModelBoxConditions F ψ σ ℓ w A q a ∧
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier),
        ∃ hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)),
          (∀ k ∈ K,
            (∀ M, (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) (k.val * M) =
              (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) M) ∧
              normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1) ∧
          ∀ g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier,
            g.val ∈ box F A q a →
              (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
                glModelFunction ψ (m + 1) σ ℓ w g := by
  obtain ⟨A₀, hA₀⟩ := exists_rankOneEmbedding_support F.canonicalTopologicalData ψ σ hσ ℓ w
  have hA : 0 ≤ max A₀ 0 := le_max_right _ _
  have hsupp : ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier,
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) ∈ 𝓛 (max A₀ 0) :=
    fun g h => lattice_mono F (le_max_left _ _) (hA₀ g h)
  have hq : min (F.canonicalTopologicalData.additiveConductor ψ) 0 ≤ 0 := min_le_right _ _
  have hψ : ∀ z ∈ 𝓛 (min (F.canonicalTopologicalData.additiveConductor ψ) 0), ψ z = 1 :=
    (F.canonicalTopologicalData.additiveTrivialAt_iff_le_conductor ψ _).2 (min_le_left _ _)
  set A : ℤ := max A₀ 0 with hAdef
  set q : ℤ := min (F.canonicalTopologicalData.additiveConductor ψ) 0 with hqdef
  obtain ⟨Kw, hKw⟩ := glModel_isSmooth ψ (m + 1) σ hσ ℓ w
  have hrow : IsOpen {g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier |
      ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} := by
    have h : {g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier |
        ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} =
        ⋂ j, ⋂ (_ : j ≠ 0), (fun g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier =>
          g.val 0 j) ⁻¹' (𝓛 (q - A) : Set F.Carrier) := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      (isOpen_lattice F _).preimage (Units.continuous_val.matrix_elem 0 j)
  let KD := Kw.comap (determinantRankOne (m + 1)) (continuous_determinantRankOne (m + 1))
  have hU : ((Kw ⊓ KD : OpenSubgroup _) : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) ∩
      {g | ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} ∈
        𝓝 (1 : Langlands.GeneralLinear (m + 1 + 1) F.Carrier) := by
    refine Filter.inter_mem ((Kw ⊓ KD).isOpen.mem_nhds (one_mem _)) (hrow.mem_nhds fun j hj => ?_)
    change (1 : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F.Carrier) 0 j ∈ 𝓛 (q - A)
    rw [Matrix.one_apply_ne (Ne.symm hj)]
    exact zero_mem _
  obtain ⟨a, ha, haU⟩ := exists_pos_principalLevelOpenSubgroup_subset F.Carrier (m + 1) hU
  have hmemU : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a,
      y ∈ ((Kw ⊓ KD : OpenSubgroup _) : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) ∩
        {g | ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} := fun y hy => haU hy
  have hL : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A) := fun y hy => (hmemU y hy).2
  have hstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ y w = w := hKw ⟨y, (hmemU y hy).1.1⟩
    rw [← glModelFunction_translate, hfix]
  have hlev : ∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 q := by
    intro z hz
    obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup ha
      (1 + Matrix.single (0 : Fin (m + 1 + 1)) (Fin.succ 0) z) (by
        intro i l
        rw [Matrix.add_apply, add_sub_cancel_left, Matrix.single_apply]
        split_ifs
        · exact hz
        · exact zero_mem_levelSet a)
    have h := hL E hE (Fin.succ 0) (Fin.succ_ne_zero 0)
    have he : E.val 0 (Fin.succ 0) = z := by
      rw [hEv, Matrix.add_apply, Matrix.one_apply_ne (Fin.succ_ne_zero 0).symm,
        Matrix.single_apply_same, zero_add]
    rw [he] at h
    exact lattice_mono F (by omega) h
  have hDstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ (determinantRankOne (m + 1) y) w = w :=
      hKw ⟨determinantRankOne (m + 1) y, (hmemU y hy).1.2⟩
    rw [← glModelFunction_translate, hfix]
  let Φ : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier := compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)
  obtain ⟨K₀, hK₀, hΦ⟩ := GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨K, hK, hsub⟩ := F.canonicalTopologicalData.generalLinearCompactOpen (m + 1 + 1)
    (((K₀ ⊓ KD : OpenSubgroup _) : Set _)) ((K₀ ⊓ KD).isOpen.mem_nhds (one_mem _))
  refine ⟨A, q, a, ⟨ha, hA, hq, hL, hψ, hlev, hstab, hsupp⟩, K, hK,
    (fun k hk => hΦ k (hsub hk).1), ?_⟩
  intro g hg
  apply averagedModelCoefficient_eq_of_left_invariant F ψ σ ℓ w hσ K hK g
  intro k hk
  have hkg : (k * g).val ∈ box F A q a := by
    have h := (hΦ k (hsub hk).1).1 g.val
    change (box F A q a).indicator (fun _ => (1 : ℂ)) (k.val * g.val) =
      (box F A q a).indicator (fun _ => (1 : ℂ)) g.val at h
    rw [Set.indicator_of_mem hg] at h
    by_contra hn
    change k.val * g.val ∉ box F A q a at hn
    rw [Set.indicator_of_notMem hn] at h
    exact zero_ne_one h
  rw [modelFunction_eq_determinantRankOne_of_mem_box F ψ σ ℓ w ha hA hq hL hψ hlev
      hstab hDstab hkg,
    modelFunction_eq_determinantRankOne_of_mem_box F ψ σ ℓ w ha hA hq hL hψ hlev
      hstab hDstab hg, map_mul]
  have hcomm : determinantRankOne (m + 1) k * determinantRankOne (m + 1) g =
      determinantRankOne (m + 1) g * determinantRankOne (m + 1) k := by
    unfold determinantRankOne
    change Iwasawa.diagonalUnits _ * Iwasawa.diagonalUnits _ =
      Iwasawa.diagonalUnits _ * Iwasawa.diagonalUnits _
    rw [← map_mul, ← map_mul, mul_comm]
  rw [hcomm, ← glModelFunction_translate]
  have hfix : glModelRepresentation ψ (m + 1) σ ℓ (determinantRankOne (m + 1) k) w = w :=
    hKw ⟨determinantRankOne (m + 1) k, (hsub hk).2⟩
  rw [hfix]

/-- The same box comparison runs in reverse: absolute matrix convergence
implies absolute rank-one convergence, and the integral has its exact positive factor. -/
theorem box_comparison_of_integrable (hσ : IsSmooth σ) {A q : ℤ} {a : ℕ}
    (hbox : ModelBoxConditions F ψ σ ℓ w A q a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      Integrable (GodementJacquet.matrixIntegrand
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a))
          (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
        (generalLinearHaar F.Carrier (m + 1)) →
      Integrable (rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          σ ℓ w s) (generalLinearHaar F.Carrier 0) ∧
      (∫ g, GodementJacquet.matrixIntegrand
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a))
          (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) g
          ∂generalLinearHaar F.Carrier (m + 1)) =
        (C : ℂ) * ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          σ ℓ w s g ∂generalLinearHaar F.Carrier 0 := by
  rcases hbox with ⟨ha, hA, hq, hL, hψ, hlev, hstab, hsupp⟩
  have hSm : MeasurableSet (boxSupport F (n := m + 1) A q a) :=
    (isOpen_boxSupport F A q a).measurableSet
  have hTm : MeasurableSet (torusBox F (n := m + 1) a) := (isOpen_torusBox F ha _).measurableSet
  have hUm : MeasurableSet (unipotentBox F (n := m + 1) q a) :=
    (isOpen_unipotentBox F q a).measurableSet
  have hC : 0 < ((generalLinearHaar F.Carrier (m + 1)).restrict
      (integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1) :
        Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))).real (boxSupport F A q a) *
      ((tailMeasure F (m + 1)).real (torusBox F a) *
        (unipotentHaar F.Carrier (m + 1)).real (unipotentBox F q a)) := by
    refine mul_pos ?_ (mul_pos ?_ ?_)
    · exact ENNReal.toReal_pos (restrict_boxSupport_pos F hA).ne'
        (restrict_boxSupport_lt_top F A q a).ne
    · exact ENNReal.toReal_pos (tailMeasure_torusBox_pos F ha _).ne'
        (tailMeasure_torusBox_lt_top F ha _).ne
    · exact ENNReal.toReal_pos (unipotentHaar_unipotentBox_pos F q a).ne'
        (unipotentHaar_unipotentBox_lt_top F hq a).ne
  refine ⟨_, hC, fun s hHint => ?_⟩
  set H := GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
    (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a))
    (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) with hH
  set Fg : Langlands.GeneralLinear (0 + 1) F.Carrier → ℂ := fun g =>
    glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (s + GodementJacquet.jpssShift (m + 1)) with hFg_def
  have hHc : Continuous H :=
    (((compactOpenIndicator (box F A q a) (isCompact_box F A q a)
      (isOpen_box F A q a)).locallyConstant.continuous.comp Units.continuous_val).mul
        (continuous_glModelFunction F ψ σ hσ ℓ w)).mul (continuous_determinantWeight F _ _)
  have hFgc : Continuous Fg :=
    ((continuous_glModelFunction F ψ σ hσ ℓ w).comp (continuous_rankOneEmbedding F m)).mul
      (continuous_determinantWeight F _ _)
  have hin : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1),
      k ∈ boxSupport F A q a →
      ∃ r : (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin (m + 1) → F.Carrierˣ)) ×
          upperUnipotent (m + 1 + 1) F.Carrier →
        (Langlands.GeneralLinear (0 + 1) F.Carrier × (Fin (m + 1) → F.Carrierˣ)) ×
          upperUnipotent (m + 1 + 1) F.Carrier,
        MeasurePreserving r (iwasawaMeasure F (m + 1)) (iwasawaMeasure F (m + 1)) ∧
          ∀ x, H (point x * k) = H (point (r x)) := by
    rintro k hk ⟨-, x₀, hx₀⟩
    obtain ⟨xβ, hβ, y, hy, rfl⟩ := exists_point_mul_of_mem_box F ha hk hx₀
    refine ⟨rshift xβ, measurePreserving_rshift F _ xβ hβ, fun x => ?_⟩
    rw [← mul_assoc, hH, matrixIntegrand_mul_principalLevel F ψ σ ℓ w hA hq hL hstab _ _ hy,
      point_rshift]
  have hout : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1),
      k ∉ boxSupport F A q a → ∀ x, H (point x * k) = 0 := by
    intro k hk hkS x
    have hnot : (point x * k).val ∉ box F A q a := fun h => hkS ⟨hk, x, h⟩
    simp only [hH, GodementJacquet.matrixIntegrand, coe_compactOpenIndicator,
      Set.indicator_of_notMem hnot, zero_mul]
  have hpoint : ∀ x, H (point x) =
      (Fg x.1.1 * (torusBox F a).indicator (fun _ => (1 : ℂ)) x.1.2) *
        (unipotentBox F q a).indicator (fun _ => (1 : ℂ)) x.2 := by
    rintro ⟨⟨g, t⟩, u⟩
    exact matrixIntegrand_point F ψ σ ℓ w ha hA hq hL hψ hlev hstab hsupp _ g t u
  have hwm : Measurable fun g : Langlands.GeneralLinear (0 + 1) F.Carrier =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  have hglOne_l : ∫⁻ g, ‖Fg g‖ₑ ∂glOneMeasure F (m + 1) =
      ∫⁻ g, ‖rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        σ ℓ w s g‖ₑ ∂generalLinearHaar F.Carrier 0 := by
    have hwm' : Measurable fun g : Langlands.GeneralLinear (0 + 1) F.Carrier =>
        ((weight F (m + 1) (g, 1) : ℝ≥0) : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hwm
    rw [glOneMeasure, lintegral_withDensity_eq_lintegral_mul _ hwm' hFgc.measurable.enorm]
    refine lintegral_congr fun g => ?_
    rw [Pi.mul_apply, ← weight_smul_integrand F ψ σ ℓ w s g, NNReal.smul_def, enorm_smul,
      NNReal.enorm_eq]
  have hglOne_i : ∫ g, Fg g ∂glOneMeasure F (m + 1) =
      ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        σ ℓ w s g ∂generalLinearHaar F.Carrier 0 := by
    rw [glOneMeasure, integral_withDensity_eq_integral_smul hwm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
      weight_smul_integrand F ψ σ ℓ w s g)
  have hnorm : ∫⁻ g, ‖H g‖ₑ ∂generalLinearHaar F.Carrier (m + 1) =
      (generalLinearHaar F.Carrier (m + 1)).restrict
        (integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1) :
          Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) (boxSupport F A q a) *
      ((∫⁻ g, ‖rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          σ ℓ w s g‖ₑ ∂generalLinearHaar F.Carrier 0) *
        (tailMeasure F (m + 1) (torusBox F a) *
          unipotentHaar F.Carrier (m + 1) (unipotentBox F q a))) := by
    rw [lintegral_enorm_eq_of_support F H hHc _ hSm hin hout,
      lintegral_param_of_eq F H Fg _ _ hTm hUm hpoint hFgc.measurable, hglOne_l]
  have hfin : ∫⁻ g, ‖rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
      σ ℓ w s g‖ₑ ∂generalLinearHaar F.Carrier 0 < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hm := hHint.2
    change ∫⁻ g, ‖H g‖ₑ ∂generalLinearHaar F.Carrier (m + 1) < ⊤ at hm
    rw [hnorm, htop] at hm
    simp [(restrict_boxSupport_pos F hA).ne',
      (tailMeasure_torusBox_pos F ha (m + 1)).ne',
      (unipotentHaar_unipotentBox_pos F q a).ne'] at hm
  have hrankc : Continuous (rankOneModelIntegrand ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) σ ℓ w s) :=
    ((continuous_glModelFunction F ψ σ hσ ℓ w).comp (continuous_rankOneEmbedding F m)).mul
      (continuous_determinantWeight F _ _)
  refine ⟨⟨hrankc.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_of_support F H hHc _ hSm hin hout hHint,
    integral_param_of_eq F H Fg _ _ hTm hUm hpoint, hglOne_i, Complex.real_smul]
  push_cast
  ring

/-- Agreement on the box is enough for equality of the complete matrix integrands. -/
theorem box_matrixIntegrand_eq_of_eq_on_box {A q : ℤ} {a : ℕ}
    {f₁ f₂ : Langlands.GeneralLinear (m + 1 + 1) F.Carrier → ℂ}
    (heq : ∀ g, g.val ∈ box F A q a → f₁ g = f₂ g) (s : ℂ) :
    GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)) s f₁ =
      GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData)
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)) s f₂ := by
  funext g
  by_cases hg : g.val ∈ box F A q a
  · simp only [GodementJacquet.matrixIntegrand, coe_compactOpenIndicator,
      Set.indicator_of_mem hg, heq g hg]
  · simp only [GodementJacquet.matrixIntegrand, coe_compactOpenIndicator,
      Set.indicator_of_notMem hg, zero_mul]

/-- A common matrix half-plane for the actual coefficient model gives a common
right half-plane for every actual rank-one model integral. -/
theorem rankOneModel_convergesOnRight_of_matrix (hσ : IsSmooth σ)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    ∃ b : ℝ, ∀ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
        Integrable (rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          σ ℓ w s) (generalLinearHaar F.Carrier 0) := by
  obtain ⟨b, hb⟩ := hMatrix
  refine ⟨b, fun w s hs => ?_⟩
  obtain ⟨A, q, a, hbox, K, hK, -, heq⟩ :=
    exists_box_averagedModelCoefficient_eq F ψ σ ℓ w hσ
  obtain ⟨C, -, hcomp⟩ := box_comparison_of_integrable F ψ σ ℓ w hσ hbox
  apply (hcomp s ?_).1
  have hm := hb (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
    (isOpen_box F A q a)) (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w) s hs
  change Integrable _ _ at hm
  rwa [box_matrixIntegrand_eq_of_eq_on_box F heq] at hm

/-- Actual matrix analytic assertions supply a convergent rational continuation
for each specified rank-one model vector. -/
theorem rankOneModel_rationalContinuation_of_matrix (hσ : IsSmooth σ)
    (P : Polynomial ℂ)
    (hMatrix : GodementJacquet.Padic.MatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P) :
    ∃ R : RationalFunctions,
      (∃ b : ℝ, ∀ s : ℂ, b < s.re →
        Integrable (rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          σ ℓ w s) (generalLinearHaar F.Carrier 0)) ∧
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          σ ℓ w s g ∂generalLinearHaar F.Carrier 0) R := by
  obtain ⟨b, hb⟩ := rankOneModel_convergesOnRight_of_matrix F ψ σ ℓ hσ hMatrix.1
  obtain ⟨A, q, a, hbox, K, hK, -, heq⟩ :=
    exists_box_averagedModelCoefficient_eq F ψ σ ℓ w hσ
  obtain ⟨C, hC, hcomp⟩ := box_comparison_of_integrable F ψ σ ℓ w hσ hbox
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let Φ : GodementJacquet.MatrixTestFunction (m + 1) F.Carrier :=
    compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)
  let f := GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  obtain ⟨R, hR⟩ := hMatrix.2.1 Φ f
  refine ⟨RatFunc.C ((C : ℂ)⁻¹) * R, ⟨b, hb w⟩, ?_⟩
  apply RationalContinuationLinear.continuation_of_eq_on_right
    (hasRationalContinuation_const_mul ((C : ℂ)⁻¹) hR.2)
  obtain ⟨d, hd⟩ := hR.1
  refine ⟨d, fun s hs => ?_⟩
  have hm := hd s hs
  change Integrable _ _ at hm
  have he := box_matrixIntegrand_eq_of_eq_on_box F heq (s + GodementJacquet.jpssShift (m + 1))
  change GodementJacquet.matrixIntegrand _ Φ _ f.val = _ at he
  rw [he] at hm
  change _ = (C : ℂ)⁻¹ * ∫ g, GodementJacquet.matrixIntegrand _ Φ _ f.val g ∂_
  rw [he, (hcomp s hm).2, inv_mul_cancel_left₀ hC']

end Convergence

end Langlands.RankinSelberg.RankOneBox
