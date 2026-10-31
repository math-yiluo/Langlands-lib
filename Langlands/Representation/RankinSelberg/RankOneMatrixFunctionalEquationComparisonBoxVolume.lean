import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonOriginalExtraction

/-! # The explicit positive volume in the original box extraction

The matrix-to-block factor is the product of the actual restricted compact-group,
tail-torus and unipotent box volumes.
-/

noncomputable section

namespace Langlands.RankinSelberg.RankOneBox

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa
open UnequalRankMirabolicUnitTest QuotientIntegration
open scoped NNReal ENNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance boxVolumeTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance boxVolumeValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance boxVolumeLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance boxVolumeT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance boxVolumeMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance boxVolumeBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local instance boxVolumeUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance boxVolumeUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance boxVolumeSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance boxVolumeUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance boxVolumeUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance boxVolumeUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩

local instance boxVolumeScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance boxVolumeScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance boxVolumeQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance boxVolumeQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

/-- The exact product of the three finite box masses in the Iwasawa calculation. -/
def boxComparisonVolume (n : ℕ) (A q : ℤ) (a : ℕ) : ℝ :=
  ((generalLinearHaar F.Carrier n).restrict
    (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier))).real (boxSupport F A q a) *
    ((tailMeasure F n).real (torusBox F a) *
      (unipotentHaar F.Carrier n).real (unipotentBox F q a))

/-- Every box with the required signs and positive principal level has positive
explicit comparison volume. -/
theorem boxComparisonVolume_pos {n : ℕ} {A q : ℤ} {a : ℕ}
    (hA : 0 ≤ A) (hq : q ≤ 0) (ha : 0 < a) :
    0 < boxComparisonVolume F n A q a := by
  refine mul_pos ?_ (mul_pos ?_ ?_)
  · exact ENNReal.toReal_pos (restrict_boxSupport_pos F hA).ne'
      (restrict_boxSupport_lt_top F A q a).ne
  · exact ENNReal.toReal_pos (tailMeasure_torusBox_pos F ha n).ne'
      (tailMeasure_torusBox_lt_top F ha n).ne
  · exact ENNReal.toReal_pos (unipotentHaar_unipotentBox_pos F q a).ne'
      (unipotentHaar_unipotentBox_lt_top F hq a).ne

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ)
  (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
  (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))

/-- The original matrix-to-block comparison with its explicit positive box factor. -/
def OriginalBoxVolumeComparison (A q : ℤ) (a : ℕ)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) : Prop :=
  0 < boxComparisonVolume F (m + 1) A q a ∧
    OriginalMatrixBlockComparison F ψ ν σ ℓ w μ
      (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
        (isOpen_box F A q a)) f (boxComparisonVolume F (m + 1) A q a : ℂ)

/-- The original box integral has exactly the explicit product-volume factor
whenever its matrix integrand is integrable. -/
theorem box_matrixIntegral_eq_volume_mul (hσ : IsSmooth σ) {A q : ℤ} {a : ℕ}
    (hbox : ModelBoxConditions F ψ σ ℓ w A q a) (s : ℂ)
    (hHint : Integrable (GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
        (isOpen_box F A q a)) (s + GodementJacquet.jpssShift (m + 1))
      (glModelFunction ψ (m + 1) σ ℓ w)) (generalLinearHaar F.Carrier (m + 1))) :
    GodementJacquet.matrixIntegral (normalizedAbsoluteValue F.canonicalTopologicalData)
        (generalLinearHaar F.Carrier (m + 1))
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
          (isOpen_box F A q a)) (s + GodementJacquet.jpssShift (m + 1))
        (glModelFunction ψ (m + 1) σ ℓ w) =
      (boxComparisonVolume F (m + 1) A q a : ℂ) *
        ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          σ ℓ w s g ∂generalLinearHaar F.Carrier 0 := by
  rcases hbox with ⟨ha, hA, hq, hL, hψ, hlev, hstab, hsupp⟩
  have hSm : MeasurableSet (boxSupport F (n := m + 1) A q a) :=
    (isOpen_boxSupport F A q a).measurableSet
  have hTm : MeasurableSet (torusBox F (n := m + 1) a) := (isOpen_torusBox F ha _).measurableSet
  have hUm : MeasurableSet (unipotentBox F (n := m + 1) q a) :=
    (isOpen_unipotentBox F q a).measurableSet
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
  have hglOne_i : ∫ g, Fg g ∂glOneMeasure F (m + 1) =
      ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        σ ℓ w s g ∂generalLinearHaar F.Carrier 0 := by
    rw [glOneMeasure, integral_withDensity_eq_integral_smul hwm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
      weight_smul_integrand F ψ σ ℓ w s g)
  change (∫ g, H g ∂generalLinearHaar F.Carrier (m + 1)) = _
  rw [integral_eq_of_support F H hHc _ hSm hin hout hHint,
    integral_param_of_eq F H Fg _ _ hTm hUm hpoint, hglOne_i, Complex.real_smul]
  unfold boxComparisonVolume
  push_cast
  ring

/-- Agreement on the box gives the literal original comparison with the
explicit factor, for every compatible quotient measure. -/
theorem originalBoxVolumeComparison_of_eq_on_box (hσ : IsSmooth σ)
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    {A q : ℤ} {a : ℕ} (hbox : ModelBoxConditions F ψ σ ℓ w A q a)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ))
    (heq : ∀ g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier,
      g.val ∈ box F A q a → f.val g = glModelFunction ψ (m + 1) σ ℓ w g) :
    OriginalBoxVolumeComparison F ψ ν σ ℓ w μ A q a f := by
  obtain ⟨b, hb⟩ := hMatrix
  refine ⟨boxComparisonVolume_pos F hbox.2.1 hbox.2.2.1 hbox.1, b, fun s hs => ?_⟩
  have hm := hb (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
    (isOpen_box F A q a)) f s hs
  change Integrable _ _ at hm
  have he := box_matrixIntegrand_eq_of_eq_on_box F heq
    (s + GodementJacquet.jpssShift (m + 1))
  rw [he] at hm
  rw [unequalRankIntegralAt_rankOne_one ψ _ ν σ ℓ w μ hμ]
  change (∫ g, GodementJacquet.matrixIntegrand _ _ _ f.val g ∂_) = _
  rw [he]
  exact box_matrixIntegral_eq_volume_mul F ψ σ ℓ w hσ hbox s hm

/-- Choose the box and actual averaged coefficient while keeping every choice
and the exact explicit positive-volume comparison. -/
theorem exists_originalBoxVolumeComparison (hσ : IsSmooth σ)
    (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    ∃ (A q : ℤ) (a : ℕ), ModelBoxConditions F ψ σ ℓ w A q a ∧
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier),
        ∃ hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)),
          (∀ k ∈ K,
            (∀ M, (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) (k.val * M) =
              (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) M) ∧
              normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1) ∧
          (∀ g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier,
            g.val ∈ box F A q a →
              (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
                glModelFunction ψ (m + 1) σ ℓ w g) ∧
          OriginalBoxVolumeComparison F ψ ν σ ℓ w μ A q a
            (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w) := by
  obtain ⟨A, q, a, hbox, K, hK, hInv, heq⟩ :=
    exists_box_averagedModelCoefficient_eq F ψ σ ℓ w hσ
  refine ⟨A, q, a, hbox, K, hK, hInv, heq, ?_⟩
  exact originalBoxVolumeComparison_of_eq_on_box F ψ ν σ ℓ w μ hσ hμ hMatrix hbox
    (GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w) heq

end Langlands.RankinSelberg.RankOneBox
