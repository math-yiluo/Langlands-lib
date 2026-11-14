import Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell
/-!
# Haar measure of `GL_(t+1)` in two-block parabolic coordinates

For the upper parabolic `P` of the block shape `(m 0 + 1, m 1 + 1)`, every element
of `P` is `parabolicPoint (L, x) = leviEmbedding L * upperRadical x`, whose matrix is
`[[a, a x], [0, d]]` for `L = (a, d)`. With the parameter measure
`parabolicMeasure = (∏ normalized block Haar measures) × dx` (no density), left
translation in `P` is measure preserving, and for every compact open `K` with
`GL_(t+1) = P K` the Haar measure of `GL_(t+1)` factors through `K × P`
(Godement–Jacquet 1972, printed page 38, in its two-block form).
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet.TwoBlock hiding glSecondCountable instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_mul_left_radical_iff integral_mul_left_radical map_mul_left_radical matrixLocallyCompact matrixSecondCountable measurableEmbedding_mul_left_radical measurable_parabolicPoint measurePreserving_parabolicShift parabolicMeasure parabolicMeasure_isFiniteMeasureOnCompacts parabolicMeasure_isOpenPosMeasure parabolicMeasure_preimage_ne_top parabolicMeasure_preimage_ne_zero parabolicMeasure_sigmaFinite parabolicPoint_translation
open Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open Langlands.GeneralLinear
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation

universe uF uR

section Algebra



end Algebra

section Topology


end Topology

section Measure

open scoped ENNReal

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local instance glSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n F) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance matrixLocallyCompact (r s : ℕ) :
    LocallyCompactSpace (Matrix (Fin r) (Fin s) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin r → Fin s → F))

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The parameter measure `dL × dx` on `Levi × Mat_{(m 0 + 1) × (m 1 + 1)}`, with the
normalized Haar measures of the blocks and a supplied measure `dx` on the radical. -/
def parabolicMeasure (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) :
    Measure ((succBlockShape m h).Levi F ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
  (Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)).prod dx

local instance matrixSecondCountable (r s : ℕ) :
    SecondCountableTopology (Matrix (Fin r) (Fin s) F) :=
  inferInstanceAs (SecondCountableTopology (Fin r → Fin s → F))

theorem measurable_parabolicPoint :
    Measurable (parabolicPoint h (R := F)) :=
  (continuous_parabolicPoint h F).measurable

variable (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
  [dx.IsAddHaarMeasure]

instance parabolicMeasure_sigmaFinite : SigmaFinite (parabolicMeasure F h dx) := by
  unfold parabolicMeasure
  infer_instance

instance parabolicMeasure_isOpenPosMeasure : (parabolicMeasure F h dx).IsOpenPosMeasure := by
  unfold parabolicMeasure
  infer_instance

instance parabolicMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (parabolicMeasure F h dx) := by
  unfold parabolicMeasure
  infer_instance

/-- Left translations of the parabolic are measure-preserving in parabolic coordinates. -/
theorem measurePreserving_parabolicShift
    (z₀ : (succBlockShape m h).Levi F × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    MeasurePreserving (parabolicShift h z₀) (parabolicMeasure F h dx) (parabolicMeasure F h dx) := by
  let c : (succBlockShape m h).Levi F → Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F :=
    fun L => (((z₀.1⁻¹ * L) 0)⁻¹ : GeneralLinear (m 0 + 1) F).val * z₀.2 *
      ((z₀.1⁻¹ * L) 1).val
  have hc : Continuous c := by
    have hL : Continuous fun L : (succBlockShape m h).Levi F => z₀.1⁻¹ * L :=
      continuous_const.mul continuous_id
    exact ((Units.continuous_val.comp (continuous_inv.comp
      ((continuous_apply (0 : Fin 2)).comp hL))).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.comp ((continuous_apply (1 : Fin 2)).comp hL))
  have hg : Measurable (Function.uncurry fun (L : (succBlockShape m h).Levi F)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) => x - c L) :=
    (continuous_snd.sub (hc.comp continuous_fst)).measurable
  exact MeasurePreserving.skew_product (g := fun L x => x - c L)
    (measurePreserving_mul_left (Measure.pi fun i : Fin 2 => generalLinearHaar F (m i))
      z₀.1⁻¹) hg
    (Filter.Eventually.of_forall fun L => map_sub_right_eq_self dx _)

/-- The parameter-space form of left translation required by the factorization integral. -/
theorem parabolicPoint_translation
    (z₀ : (succBlockShape m h).Levi F × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    ∃ σ, MeasurePreserving σ (parabolicMeasure F h dx) (parabolicMeasure F h dx) ∧
      ∀ z, parabolicPoint h (σ z) = (parabolicPoint h z₀)⁻¹ * parabolicPoint h z :=
  ⟨parabolicShift h z₀, measurePreserving_parabolicShift F h dx z₀,
    parabolicPoint_parabolicShift h z₀⟩

/-- The parameters of an open subgroup have positive measure. -/
theorem parabolicMeasure_preimage_ne_zero (K : OpenSubgroup (GeneralLinear (t + 1) F)) :
    parabolicMeasure F h dx (parabolicPoint h ⁻¹' (K : Set (GeneralLinear (t + 1) F))) ≠
      0 :=
  (K.isOpen.preimage (continuous_parabolicPoint h F)).measure_ne_zero _
    ⟨(1, 0), by simp⟩

/-- The parameters of a compact subgroup have finite measure. -/
theorem parabolicMeasure_preimage_ne_top (K : Subgroup (GeneralLinear (t + 1) F))
    (hK : IsCompact (K : Set (GeneralLinear (t + 1) F))) :
    parabolicMeasure F h dx (parabolicPoint h ⁻¹' (K : Set (GeneralLinear (t + 1) F))) ≠
      ∞ := by
  have hc : IsCompact (parabolicCoord h '' ((Subtype.val :
      (succBlockShape m h).parabolic F → GeneralLinear (t + 1) F) ⁻¹'
        (K : Set (GeneralLinear (t + 1) F)))) :=
    (((succBlockShape m h).isClosed_parabolic F).isClosedEmbedding_subtypeVal.isCompact_preimage
      hK).image (continuous_parabolicCoord h F)
  have hsub : parabolicPoint h ⁻¹' (K : Set (GeneralLinear (t + 1) F)) ⊆
      parabolicCoord h '' ((Subtype.val :
        (succBlockShape m h).parabolic F → GeneralLinear (t + 1) F) ⁻¹'
          (K : Set (GeneralLinear (t + 1) F))) := by
    intro z hz
    exact ⟨⟨parabolicPoint h z, parabolicPoint_mem h z⟩, hz, parabolicCoord_parabolicPoint h z⟩
  exact (lt_of_le_of_lt (measure_mono hsub) hc.measure_lt_top).ne

section Scaling

open scoped NNReal

/-- Left multiplication by `a ∈ GL_(m 0 + 1)` scales the radical measure by `|det a|^(-(m 1 + 1))`. -/
theorem map_mul_left_radical (a : GeneralLinear (m 0 + 1) F) :
    dx.map (fun x => a.val * x) =
      (((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) a : ℝ≥0) ^ (m 1 + 1))⁻¹ • dx := by
  have h := Langlands.AllField.HarmonicAnalysis.padicRectangularHaarScaling F (⟨⟩ : LocalFieldData F)
    (m 0 + 1) (m 1 + 1) dx a 1
  have he : (fun X : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F =>
      (a : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) * X *
        ((1⁻¹ : GeneralLinear (m 1 + 1) F) : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F)) =
      fun X => a.val * X := by
    funext X
    simp
  rw [he, map_one, Units.val_one, one_pow, div_one] at h
  exact h

theorem measurableEmbedding_mul_left_radical (a : GeneralLinear (m 0 + 1) F) :
    MeasurableEmbedding (fun x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F => a.val * x) := by
  refine MeasurableEmbedding.of_measurable_inverse
    (continuous_const.matrix_mul continuous_id).measurable ?_
    (g := fun x => (a⁻¹ : GeneralLinear (m 0 + 1) F).val * x)
    (continuous_const.matrix_mul continuous_id).measurable ?_
  · have : Set.range (fun x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F => a.val * x) =
        Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      refine ⟨(a⁻¹ : GeneralLinear (m 0 + 1) F).val * y, ?_⟩
      change a.val * ((a⁻¹ : GeneralLinear (m 0 + 1) F).val * y) = y
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [this]
    exact MeasurableSet.univ
  · intro x
    change (a⁻¹ : GeneralLinear (m 0 + 1) F).val * (a.val * x) = x
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

/-- **Radical scaling.** `∫ Ψ (a x) dx = |det a|^(-(m 1 + 1)) ∫ Ψ dx`. -/
theorem integral_mul_left_radical {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : GeneralLinear (m 0 + 1) F) (Ψ : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → E) :
    ∫ x, Ψ (a.val * x) ∂dx =
      ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) a : ℝ≥0) : ℝ) ^ (m 1 + 1))⁻¹ •
        ∫ y, Ψ y ∂dx := by
  rw [← (measurableEmbedding_mul_left_radical F a).integral_map, map_mul_left_radical,
    integral_smul_nnreal_measure]
  rw [NNReal.smul_def]
  push_cast
  rfl

/-- Integrability is unchanged by the radical scaling. -/
theorem integrable_mul_left_radical_iff {E : Type*} [NormedAddCommGroup E]
    (a : GeneralLinear (m 0 + 1) F) (Ψ : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → E) :
    Integrable (fun x => Ψ (a.val * x)) dx ↔ Integrable Ψ dx := by
  change Integrable (Ψ ∘ fun x => a.val * x) dx ↔ _
  rw [← (measurableEmbedding_mul_left_radical F a).integrable_map_iff, map_mul_left_radical,
    ENNReal.smul_def]
  refine integrable_smul_measure ?_ ?_
  · simp
  · simp

end Scaling

section Factorization


end Factorization

end Measure

end Langlands.AllField.GodementJacquet.TwoBlock
