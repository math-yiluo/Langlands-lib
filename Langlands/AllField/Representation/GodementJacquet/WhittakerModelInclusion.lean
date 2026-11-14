import Langlands.Representation.GodementJacquet.WhittakerModelInclusion
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.GodementJacquet.ModelWhittakerRationalityStatement
import Langlands.AllField.Representation.GodementJacquet.WhittakerAveraging
import Langlands.AllField.Representation.GodementJacquet.WhittakerModelComparisonStatement
import Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof
/-!
# Matrix-coefficient integrals of the model as sums of Whittaker integrals

JPSS (1983), Section (5.2), printed 421: on an admissible coefficient model, every
smooth functional agrees with a finite combination of compact averages of
evaluations, and a conjugation change of variables turns each resulting integral
into a full-matrix Whittaker integral. Given convergence and rationality of every
Whittaker integral on the model, this gives `I₂ ⊆ I₃`.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open scoped ENNReal NNReal BigOperators

universe uF uV uG

section Invariant


end Invariant

section ShiftedValues

end ShiftedValues

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair ModelRationality NormalizedMatrixFunctionalEquationData averagingBorelSpace averagingLocalField averagingMeasurableSpace averagingSecondCountable averagingSigmaCompact averagingTopology averagingValuativeRel conjTest conjTest_apply exists_compactOpen_matrixTest_invariant exists_eq_sum_modelPointAverage exists_mem_jpssI3_of_coefficient exists_nhds_matrixTest_invariant exists_whittakerRationalValue glModelFunction_injective glModel_isAdmissible instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_conj_iff integral_conj iotaMatrixRationalValues jpssI2 jpssI2_le_jpssI3_of_rationality jpssI3 jpssI3_le_jpssI2 matrixIntegral matrixIntegral_sum_modelPointAverage matrixIntegrand matrixIntegrand_conj matrixRationalValues matrixRationalValues_subset_jpssI3 measurableEmbedding_conj measurePreserving_conj measureReal_openSubgroup_ne_zero modelInclusionBorelSpace modelInclusionLocalField modelInclusionMeasurableSpace modelInclusionSecondCountable modelInclusionSigmaCompact modelInclusionTopology modelInclusionValuativeRel modelPointAverage modelPointAverage_apply modelPointAverage_invariant modelPointAverage_matrixIntegral modelPointAverage_of_mem_fixedVectors modelSetIntegral modelSetIntegralDual whittakerRationalValues whittakerRationalValues_subset
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair ModelWhittakerRationalityStatement NormalizedMatrixFunctionalEquationData WhittakerModelComparisonStatement iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerModelComparison_of_rationality whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelInclusionMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance modelInclusionBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance modelInclusionSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance modelInclusionSigmaCompact (n : ℕ) : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (n + 1)

variable {n : ℕ}

section Conjugation

/-- The conjugated test function `M ↦ Φ(h⁻¹ M h)`, again Schwartz–Bruhat on all
square matrices. -/
def conjTest (Φ : MatrixTestFunction n F)
    (h : Langlands.GeneralLinear (n + 1) F) : MatrixTestFunction n F :=
  let e : Matrix (Fin (n + 1)) (Fin (n + 1)) F ≃ₜ
      Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    { toFun := fun M => (h⁻¹ : Langlands.GeneralLinear (n + 1) F).val * M * h.val
      invFun := fun M => h.val * M * (h⁻¹ : Langlands.GeneralLinear (n + 1) F).val
      left_inv := fun M => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mul]
        simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]
      right_inv := fun M => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]
        simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun :=
        (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  ⟨fun M => Φ (e M), Φ.locallyConstant.comp_continuous e.continuous,
    Φ.hasCompactSupport.comp_homeomorph e⟩

@[simp] theorem conjTest_apply (Φ : MatrixTestFunction n F)
    (h : Langlands.GeneralLinear (n + 1) F) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    conjTest F Φ h M = Φ ((h⁻¹ : Langlands.GeneralLinear (n + 1) F).val * M * h.val) :=
  rfl

/-- The pointwise identity behind the conjugation change of variables. -/
theorem matrixIntegrand_conj (Φ : MatrixTestFunction n F)
    (h : Langlands.GeneralLinear (n + 1) F) (u : Langlands.GeneralLinear (n + 1) F → ℂ)
    (s : ℂ) (g : Langlands.GeneralLinear (n + 1) F) :
    GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (conjTest F Φ h) s (fun y => u (y * h)) (h * g * h⁻¹) =
      Φ g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s *
        u (h * g) := by
  have hM : (h⁻¹ : Langlands.GeneralLinear (n + 1) F).val * (h * g * h⁻¹).val * h.val =
      g.val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hdet : Matrix.det (h * g * h⁻¹).val = Matrix.det g.val := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det h.val),
      mul_assoc, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      mul_one]
  have hu : h * g * h⁻¹ * h = h * g := by group
  simp only [GodementJacquet.matrixIntegrand, conjTest_apply, hM, hu, determinantWeight, hdet]
  ring

end Conjugation

section ConjugationIntegral

/-- Conjugation by a fixed element preserves the normalized Haar measure. -/
theorem measurePreserving_conj (h : Langlands.GeneralLinear (n + 1) F) :
    MeasurePreserving (fun g => h * g * h⁻¹) (generalLinearHaar F n)
      (generalLinearHaar F n) :=
  (measurePreserving_mul_right _ h⁻¹).comp (measurePreserving_mul_left _ h)

/-- Conjugation by a fixed element is a measurable embedding. -/
theorem measurableEmbedding_conj (h : Langlands.GeneralLinear (n + 1) F) :
    MeasurableEmbedding fun g : Langlands.GeneralLinear (n + 1) F => h * g * h⁻¹ :=
  (measurableEmbedding_mulRight h⁻¹).comp (measurableEmbedding_mulLeft h)

/-- Conjugation change of variables, integrability: `Φ(g) |det g|^s u(hg)` is
integrable exactly when the matrix integrand of the conjugated test against the
right translate `y ↦ u(yh)` is. -/
theorem integrable_conj_iff (Φ : MatrixTestFunction n F)
    (h : Langlands.GeneralLinear (n + 1) F)
    (u : Langlands.GeneralLinear (n + 1) F → ℂ) (s : ℂ) :
    Integrable (fun g => Φ g.val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s * u (h * g))
        (generalLinearHaar F n) ↔
      MatrixConverges F (conjTest F Φ h) s (fun y => u (y * h)) := by
  have e := (measurePreserving_conj F h).integrable_comp_emb (measurableEmbedding_conj F h)
    (g := GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (conjTest F Φ h) s (fun y => u (y * h)))
  have hfun : (GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (conjTest F Φ h) s (fun y => u (y * h)) ∘ fun g => h * g * h⁻¹) =
      fun g => Φ g.val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s * u (h * g) :=
    funext fun g => matrixIntegrand_conj F Φ h u s g
  rw [hfun] at e
  exact e

/-- Conjugation change of variables, value. -/
theorem integral_conj (Φ : MatrixTestFunction n F)
    (h : Langlands.GeneralLinear (n + 1) F)
    (u : Langlands.GeneralLinear (n + 1) F → ℂ) (s : ℂ) :
    ∫ g, Φ g.val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s * u (h * g)
        ∂(generalLinearHaar F n) =
      matrixIntegral F (conjTest F Φ h) s (fun y => u (y * h)) := by
  have e := (measurePreserving_conj F h).integral_comp (measurableEmbedding_conj F h)
    (GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (conjTest F Φ h) s (fun y => u (y * h)))
  simp only [matrixIntegrand_conj] at e
  exact e

end ConjugationIntegral

section PointAverage

variable (ψ : UnitaryAdditiveCharacter F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- A vector of the coefficient model is determined by its model function. -/
theorem glModelFunction_injective (ℓ : glFunctionals ψ n σ) :
    Function.Injective (glModelFunction ψ n σ ℓ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

/-- The functional `W ↦ ∫_L W(hk) dk` on the model, for a compact open subgroup `L`. -/
def modelPointAverage (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)))
    (h : Langlands.GeneralLinear (n + 1) F) :
    Module.Dual ℂ (glCoefficientModel ψ n σ ℓ).toSubmodule where
  toFun W := ∫ k in (L : Set (Langlands.GeneralLinear (n + 1) F)),
    glModelFunction ψ n σ ℓ W (h * k) ∂(generalLinearHaar F n)
  map_add' W₁ W₂ := by
    have hh : Continuous fun k : Langlands.GeneralLinear (n + 1) F => h * k :=
      continuous_const.mul continuous_id
    have h₁ : IntegrableOn (fun k => glModelFunction ψ n σ ℓ W₁ (h * k))
        (L : Set (Langlands.GeneralLinear (n + 1) F)) (generalLinearHaar F n) :=
      ((glModelFunction_continuous ψ n σ hσ ℓ W₁).comp hh).continuousOn.integrableOn_compact'
        hL L.isOpen.measurableSet
    have h₂ : IntegrableOn (fun k => glModelFunction ψ n σ ℓ W₂ (h * k))
        (L : Set (Langlands.GeneralLinear (n + 1) F)) (generalLinearHaar F n) :=
      ((glModelFunction_continuous ψ n σ hσ ℓ W₂).comp hh).continuousOn.integrableOn_compact'
        hL L.isOpen.measurableSet
    rw [← integral_add h₁ h₂]
    rfl
  map_smul' c W := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    rfl

/-- Unfolding the point average. -/
theorem modelPointAverage_apply (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)))
    (h : Langlands.GeneralLinear (n + 1) F) (W : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    modelPointAverage F ψ σ hσ ℓ L hL h W =
      ∫ k in (L : Set (Langlands.GeneralLinear (n + 1) F)),
        glModelFunction ψ n σ ℓ W (h * k) ∂(generalLinearHaar F n) :=
  rfl

/-- The point average is invariant under right translation by `L`. -/
theorem modelPointAverage_invariant (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)))
    (h : Langlands.GeneralLinear (n + 1) F)
    {k : Langlands.GeneralLinear (n + 1) F} (hk : k ∈ L)
    (W : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ k W) =
      modelPointAverage F ψ σ hσ ℓ L hL h W := by
  rw [modelPointAverage_apply, modelPointAverage_apply]
  simp only [glModelFunction_translate]
  have e := setIntegral_mul_right_of_mem (generalLinearHaar F n) L.toSubgroup
    L.isOpen.measurableSet hk (fun y => glModelFunction ψ n σ ℓ W (h * y))
  simp only [mul_assoc] at e ⊢
  exact e

/-- On vectors fixed by `L`, the point average is `vol(L)` times evaluation at `h`. -/
theorem modelPointAverage_of_mem_fixedVectors (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)))
    (h : Langlands.GeneralLinear (n + 1) F)
    {W : (glCoefficientModel ψ n σ ℓ).toSubmodule}
    (hW : W ∈ fixedVectors (glModelRepresentation ψ n σ ℓ) L.toSubgroup) :
    modelPointAverage F ψ σ hσ ℓ L hL h W =
      ((generalLinearHaar F n).real (L : Set (Langlands.GeneralLinear (n + 1) F)) :
        ℂ) * glModelFunction ψ n σ ℓ W h := by
  rw [modelPointAverage_apply]
  have hc : Set.EqOn (fun k => glModelFunction ψ n σ ℓ W (h * k))
      (fun _ => glModelFunction ψ n σ ℓ W h)
      (L : Set (Langlands.GeneralLinear (n + 1) F)) := by
    intro k hk
    have e : glModelRepresentation ψ n σ ℓ k W = W := hW ⟨k, hk⟩
    have e' := congrArg (fun W' => glModelFunction ψ n σ ℓ W' h) e
    simpa only [glModelFunction_translate] using e'
  rw [setIntegral_congr_fun L.isOpen.measurableSet hc, setIntegral_const, Complex.real_smul]

/-- A compact open subgroup has nonzero finite Haar mass. -/
theorem measureReal_openSubgroup_ne_zero (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F))) :
    ((generalLinearHaar F n).real (L : Set (Langlands.GeneralLinear (n + 1) F)) :
      ℂ) ≠ 0 := by
  have hLfin : generalLinearHaar F n (L : Set (Langlands.GeneralLinear (n + 1) F)) ≠ ⊤ :=
    hL.measure_lt_top.ne
  have hLpos : generalLinearHaar F n (L : Set (Langlands.GeneralLinear (n + 1) F)) ≠ 0 :=
    (L.isOpen.measure_pos (generalLinearHaar F n) ⟨1, L.one_mem⟩).ne'
  rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
  exact not_or.mpr ⟨hLpos, hLfin⟩

/-- A vector fixed by `L` on which every point average vanishes is zero. -/
theorem eq_zero_of_modelPointAverage_eq_zero (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)))
    {W : (glCoefficientModel ψ n σ ℓ).toSubmodule}
    (hW : W ∈ fixedVectors (glModelRepresentation ψ n σ ℓ) L.toSubgroup)
    (h0 : ∀ h, modelPointAverage F ψ σ hσ ℓ L hL h W = 0) : W = 0 := by
  apply glModelFunction_injective F ψ σ ℓ
  funext h
  have h1 := h0 h
  rw [modelPointAverage_of_mem_fixedVectors F ψ σ hσ ℓ L hL h hW] at h1
  exact ((mul_eq_zero.mp h1).resolve_left (measureReal_openSubgroup_ne_zero F L hL)).trans rfl

/-- On an admissible coefficient model, every smooth functional agrees with a finite
combination of point averages over some compact open subgroup inside a prescribed
open subgroup. -/
theorem exists_eq_sum_modelPointAverage (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (Λ : SmoothDual (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (U : OpenSubgroup (Langlands.GeneralLinear (n + 1) F)) :
    ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      ∃ hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)), L ≤ U ∧
      ∃ (t : Finset (Langlands.GeneralLinear (n + 1) F))
        (c : Langlands.GeneralLinear (n + 1) F → ℂ),
        ∀ W, Λ.val W = ∑ h ∈ t, c h * modelPointAverage F ψ σ hσ ℓ L hL h W := by
  obtain ⟨K₀, hK₀⟩ := Λ.property
  obtain ⟨L, hLc, hLU⟩ := Langlands.AllField.Unramified.SphericalExistence.exists_compactOpenSubgroup_le F (K₀ ⊓ U)
  obtain ⟨c, hc⟩ := exists_eq_sum_of_invariant (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (glModelRepresentation ψ n σ ℓ) (glModel_isSmooth ψ n σ hσ ℓ) L hLc (hadm.2 L)
    (fun h => modelPointAverage F ψ σ hσ ℓ L hLc h)
    (fun h _ hk W => modelPointAverage_invariant F ψ σ hσ ℓ L hLc h hk W) Λ.val
    (fun _ hk W => apply_of_mem_fixedVectors_dual _ _ hK₀ (hLU hk).1 W)
    (fun e he h0 => by
      rw [eq_zero_of_modelPointAverage_eq_zero F ψ σ hσ ℓ L hLc he h0, map_zero])
  exact ⟨L, hLc, fun k hk => (hLU hk).2, c.support, c, hc⟩

end PointAverage

section ModelInclusion

variable (ψ : UnitaryAdditiveCharacter F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- JPSS (1983), printed 421: integrating the point average of the right translates
of a model vector against `Φ(g)|det g|^s`, for `L` fixing `Φ` on the left and inside
the kernel of `|det|`, gives `vol(L)` times the Whittaker integral of the conjugated
test function at the right translate by `h`. -/
theorem modelPointAverage_matrixIntegral (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (Φ : MatrixTestFunction n F)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)))
    (hLΦ : ∀ k ∈ L, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1)
    (h : Langlands.GeneralLinear (n + 1) F)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) (s : ℂ)
    (hconv : MatrixConverges F (conjTest F Φ h) s
      (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w))) :
    Integrable (fun g => Φ g.val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s *
        modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w))
        (generalLinearHaar F n) ∧
      ∫ g, Φ g.val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s *
        modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)
        ∂(generalLinearHaar F n) =
      ((generalLinearHaar F n).real
          (L : Set (Langlands.GeneralLinear (n + 1) F)) : ℂ) *
        matrixIntegral F (conjTest F Φ h) s
          (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w)) := by
  let G := Langlands.GeneralLinear (n + 1) F
  let abv := normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
  let μ := generalLinearHaar F n
  let W := glModelFunction ψ n σ ℓ w
  let a : G → ℂ := fun g => Φ g.val * determinantWeight abv g s
  have ha : ∀ x ∈ (L : Set G), ∀ g, a (x * g) = a g := by
    intro x hx g
    obtain ⟨hΦx, hdet⟩ := hLΦ x hx
    have e : (x * g).val = x.val * g.val := rfl
    have hdet' : abv x.val.det = 1 := hdet
    show Φ (x * g).val * determinantWeight abv (x * g) s =
      Φ g.val * determinantWeight abv g s
    rw [determinantWeight, determinantWeight, e, hΦx, Matrix.det_mul, AbsoluteValue.map_mul,
      hdet', one_mul]
  have hint : Integrable (fun g => a g * W (h * g)) μ :=
    (integrable_conj_iff F Φ h W s).mpr hconv
  obtain ⟨h1, h2⟩ := leftAverage_integral μ (L : Set G) L.isOpen.measurableSet
    hL.measure_lt_top.ne a (fun x => W (h * x)) ha hint
  have hfun : (fun g => Φ g.val * determinantWeight abv g s *
      modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)) =
      fun g => a g * ∫ x in (L : Set G), W (h * (x * g)) ∂μ := by
    funext g
    show a g * _ = a g * _
    rw [modelPointAverage_apply]
    congr 1
    refine setIntegral_congr_fun L.isOpen.measurableSet fun x _ => ?_
    show glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ g w) (h * x) =
      glModelFunction ψ n σ ℓ w (h * (x * g))
    rw [glModelFunction_translate, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact h1
  · rw [hfun, h2]
    congr 1
    exact integral_conj F Φ h W s

/-- The admissibility of `σ` passes to its coefficient model. -/
theorem glModel_isAdmissible (ℓ : glFunctionals ψ n σ) (hσ : IsAdmissible σ) :
    IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) :=
  Unramified.SphericalExistence.isAdmissible_of_surjective
    (Langlands.AllField.Unramified.SphericalExistence.exists_compactOpenSubgroup_le F) (modelMap σ ℓ)
    (modelMap_surjective σ ℓ) hσ

/-- The local form of `ModelWhittakerRationalityStatement`: every shifted Whittaker
integral on the model converges on a right half-plane and is rational. -/
def ModelRationality (ℓ : glFunctionals ψ n σ) : Prop :=
  ∀ (Φ : MatrixTestFunction n F) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule),
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      MatrixConverges F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) ∧
    ∃ R : RationalFunctions,
      HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
        (fun s => matrixIntegral F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) R

/-- A Whittaker integral of the model has a rational value lying in `I₃`, with an
explicit half-plane of convergence. -/
theorem exists_whittakerRationalValue (ℓ : glFunctionals ψ n σ) (hC : ModelRationality F ψ σ ℓ)
    (Φ : MatrixTestFunction n F) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    ∃ (a : ℝ) (R : RationalFunctions),
      (∀ s : ℂ, a < s.re →
        MatrixConverges F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) ∧
      HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
        (fun s => matrixIntegral F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) R ∧
      R ∈ whittakerRationalValues F ψ σ ℓ := by
  obtain ⟨⟨a, ha⟩, R, hR⟩ := hC Φ w
  exact ⟨a, R, ha, hR, Φ, w, ⟨a, ha⟩, hR⟩

/-- The matrix integral of a finite combination of point averages of right
translates is the corresponding combination of Whittaker integrals of conjugated
test functions, wherever all of the latter converge. -/
theorem matrixIntegral_sum_modelPointAverage (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (Φ : MatrixTestFunction n F)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hL : IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)))
    (hLΦ : ∀ k ∈ L, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1)
    (t : Finset (Langlands.GeneralLinear (n + 1) F))
    (c : Langlands.GeneralLinear (n + 1) F → ℂ)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hf : ∀ g, f g = ∑ h ∈ t, c h *
      modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w))
    (s : ℂ)
    (hconv : ∀ h ∈ t, MatrixConverges F (conjTest F Φ h) s
      (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w))) :
    MatrixConverges F Φ s f ∧
      matrixIntegral F Φ s f =
        ∑ h ∈ t, c h * ((generalLinearHaar F n).real
            (L : Set (Langlands.GeneralLinear (n + 1) F)) : ℂ) *
          matrixIntegral F (conjTest F Φ h) s
            (glModelFunction ψ n σ ℓ (glModelRepresentation ψ n σ ℓ h w)) := by
  have hG2 := fun h (hh : h ∈ t) =>
    modelPointAverage_matrixIntegral F ψ σ hσ ℓ Φ L hL hLΦ h w s (hconv h hh)
  have hpt : GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      Φ s f = fun g => ∑ h ∈ t, c h * (Φ g.val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s *
        modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)) := by
    funext g
    rw [GodementJacquet.matrixIntegrand, hf g, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hint : ∀ h ∈ t, Integrable (fun g => c h * (Φ g.val *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s *
      modelPointAverage F ψ σ hσ ℓ L hL h (glModelRepresentation ψ n σ ℓ g w)))
      (generalLinearHaar F n) :=
    fun h hh => (hG2 h hh).1.const_mul (c h)
  refine ⟨?_, ?_⟩
  · show Integrable (GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Φ s f) (generalLinearHaar F n)
    rw [hpt]
    exact integrable_finsetSum t hint
  · show ∫ g, GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Φ s f g
        ∂(generalLinearHaar F n) = _
    rw [hpt, integral_finsetSum t hint]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [integral_const_mul, (hG2 h hh).2, mul_assoc]

/-- JPSS (1983), printed 421: on an admissible model with rational Whittaker
integrals, the integral of a matrix coefficient `g ↦ Λ(ρ(g)w)` of the model, for a
smooth functional `Λ`, is a finite combination of Whittaker integrals, hence has a
rational value in `I₃`. -/
theorem exists_mem_jpssI3_of_coefficient (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (hC : ModelRationality F ψ σ ℓ)
    (Λ : SmoothDual (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hf₀ : ∀ g, f g = Λ.val (glModelRepresentation ψ n σ ℓ g w))
    (Φ : MatrixTestFunction n F) :
    ∃ R ∈ jpssI3 F ψ σ ℓ,
      HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) Φ
        f R := by
  obtain ⟨K, -, hK⟩ := exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨L, hL, hLK, t, c, hc⟩ := exists_eq_sum_modelPointAverage F ψ σ hσ ℓ hadm Λ K
  choose a R ha hR hRmem using fun h : Langlands.GeneralLinear (n + 1) F =>
    exists_whittakerRationalValue F ψ σ ℓ hC (conjTest F Φ h)
      (glModelRepresentation ψ n σ ℓ h w)
  have hb : ∀ h ∈ t, a h ≤ ∑ i ∈ t, |a i| := fun h hh =>
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (a i)) hh)
  have hf : ∀ g, f g = ∑ h ∈ t, c h * modelPointAverage F ψ σ hσ ℓ L hL h
      (glModelRepresentation ψ n σ ℓ g w) :=
    fun g => (hf₀ g).trans (hc _)
  have key := fun (s : ℂ) (hs : ∑ i ∈ t, |a i| < s.re) =>
    matrixIntegral_sum_modelPointAverage F ψ σ hσ ℓ Φ L hL (fun k hk => hK k (hLK hk)) t c
      w f hf (s + jpssShift n) (fun h hh => ha h s ((hb h hh).trans_lt hs))
  refine ⟨∑ h ∈ t, RatFunc.C (c h * ((generalLinearHaar F n).real
      (L : Set (Langlands.GeneralLinear (n + 1) F)) : ℂ)) * R h, ?_,
    ⟨∑ i ∈ t, |a i|, fun s hs => (key s hs).1⟩, ?_⟩
  · exact RationalContinuationLinear.linear_combination_mem_span t _ R (fun h _ => hRmem h)
  · exact RationalContinuationLinear.continuation_of_eq_on_right
      (RationalContinuationLinear.continuation_linear_combination t _ _ R (fun h _ => hR h))
      ⟨∑ i ∈ t, |a i|, fun s hs => (key s hs).2⟩

/-- Every rational value of a bi-smooth matrix-coefficient integral of the model lies
in `I₃`, given admissibility of the model and rationality of its Whittaker integrals. -/
theorem matrixRationalValues_subset_jpssI3 (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (hC : ModelRationality F ψ σ ℓ) :
    matrixRationalValues F (n := n) (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
        (glModelRepresentation ψ n σ ℓ) ⊆ (jpssI3 F ψ σ ℓ : Set RationalFunctions) := by
  have hP : ∀ f ∈ biSmoothMatrixCoefficients (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ), ∀ Φ : MatrixTestFunction n F,
      ∃ R ∈ jpssI3 F ψ σ ℓ,
        HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n)
          Φ f R := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Λ, v, rfl⟩ := hx
      exact exists_mem_jpssI3_of_coefficient F ψ σ hσ ℓ hadm hC Λ v.val _
        (biSmoothCoefficient_apply _ Λ v)
    | zero => exact fun Φ => ⟨0, Submodule.zero_mem _, hasShiftedRationalValue_zero _⟩
    | add x y _ _ hx hy =>
      intro Φ
      obtain ⟨R₁, hR₁, h₁⟩ := hx Φ
      obtain ⟨R₂, hR₂, h₂⟩ := hy Φ
      exact ⟨R₁ + R₂, Submodule.add_mem _ hR₁ hR₂, h₁.add h₂⟩
    | smul c x _ hx =>
      intro Φ
      obtain ⟨R, hR, h⟩ := hx Φ
      exact ⟨RatFunc.C c * R, const_mul_mem_zetaSpan c hR, h.smul c⟩
  rintro R ⟨Φ, f, hR⟩
  obtain ⟨R', hR', h'⟩ := hP f.val f.property Φ
  rw [hR.2.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one h'.2]
  exact hR'

/-- `I₂ ⊆ I₃` for the actual coefficient model, given admissibility of the model and
rationality of its Whittaker integrals. -/
theorem jpssI2_le_jpssI3_of_rationality (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (hadm : IsAdmissible (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (hC : ModelRationality F ψ σ ℓ) :
    jpssI2 F (n := n) (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
        (glModelRepresentation ψ n σ ℓ) ≤ jpssI3 F ψ σ ℓ :=
  Submodule.span_le.mpr (matrixRationalValues_subset_jpssI3 F ψ σ hσ ℓ hadm hC)

end ModelInclusion

end Padic

/-- JPSS (1983), Section (5.2): `I₂ = I₃` on the actual coefficient model, assuming
convergence and rationality of every Whittaker integral on that model. -/
theorem whittakerModelComparison_of_rationality
    (hC : ModelWhittakerRationalityStatement.{uF, uV}) :
    WhittakerModelComparisonStatement.{uF, uV} := by
  intro F _ _ _ _ ψ n V _ _ σ hW ℓ hℓ
  exact le_antisymm
    (Langlands.AllField.GodementJacquet.Padic.jpssI2_le_jpssI3_of_rationality F ψ σ hW.1.1 ℓ
      (Langlands.AllField.GodementJacquet.Padic.glModel_isAdmissible F ψ σ ℓ hW.1) (hC F ψ n σ hW ℓ hℓ))
    (Langlands.AllField.GodementJacquet.Padic.jpssI3_le_jpssI2 F ψ σ hW.1.1 ℓ)

end Langlands.AllField.GodementJacquet
