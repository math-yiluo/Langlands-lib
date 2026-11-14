import Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.AllField.HarmonicAnalysis.PadicLatticeTopology
import Langlands.AllField.HarmonicAnalysis.RectangularFourierUnimodularTranslate
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement
/-!
# The dual two-block parabolic integral

Godement–Jacquet 1972, proof of Theorem 3.4 (printed pages 36–45): after the
substitution `g ↦ (g⁻¹)ᵀ`, the transformed zeta integral of an induced
representation is reduced to the Levi blocks along the coordinates
`(a, d, x) ↦ [[a, a x], [0, d]]` of the upper block parabolic. The inverse
transpose of this matrix is `[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]`, so the
radical variable `x` enters through the lower-left block. The substitution
`C = -(d⁻¹)ᵀ xᵀ` multiplies the rectangular Haar measure by `|det d|^(n₀)`, and
the lower-left partial integral of the test function then splits into the
Levi blocks.

This module proves that reduction for a test function whose lower-left partial
integral is a finite sum of tensor products, with weights `u₀, u₁` on the two
Levi blocks that are integrable against every Schwartz–Bruhat function composed
with the inverse transpose. Integrability on the product space comes from a
majorant by a product of indicators of compact open sets. The reduction is stated
both in the coordinates `((a, d), x)` and in Levi coordinates `(L, x)`. A last
section transfers finite decompositions of two-sided compact translates of a test
function to its Fourier transform evaluated at inverse transposes.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankContinuedForms isEqualRankLPolynomial_characterChange_normalized normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.HarmonicAnalysis (blockMatrix)
open scoped NNReal ENNReal

universe uF

section Transpose


end Transpose

section BlockAlgebra


end BlockAlgebra

section Majorant


end Majorant

section BlockMajorant


end BlockMajorant

namespace Padic
open Langlands.GodementJacquet.Padic hiding aestronglyMeasurable_dualParabolicIntegrand dualParabolicBorelSpace dualParabolicGLBorelSpace dualParabolicGLMeasurableSpace dualParabolicIntegrand dualParabolicLocalField dualParabolicMatrixSecondCountable dualParabolicMeasurableSpace dualParabolicSecondCountable dualParabolicT2Space dualParabolicTopology dualParabolicTotallyDisconnected dualParabolicValuativeRel integrable_comp_lowerLeft integrable_integral_dualParabolicIntegrand integrable_integral_dualParabolic_levi integral_comp_lowerLeft map_mulLeftMeasurableEquiv measurable_inverseTranspose_val mulLeftMeasurableEquiv mulLeftMeasurableEquiv_apply rectangularFourierEquiv_inverseTranspose_translate rectangularFourierEquiv_inverseTranspose_translate_of_mem
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance dualParabolicMeasurableSpace : MeasurableSpace F := borel F
local instance dualParabolicBorelSpace : BorelSpace F := ⟨rfl⟩
local instance dualParabolicSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance dualParabolicT2Space : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance dualParabolicTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance dualParabolicMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))
local instance dualParabolicGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n F) := borel _
local instance dualParabolicGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n F) := ⟨rfl⟩

/-- Left multiplication by an invertible matrix, as a measurable equivalence of
rectangular matrices. -/
def mulLeftMeasurableEquiv {r : ℕ} (A : Langlands.GeneralLinear r F) (s : ℕ) :
    Matrix (Fin r) (Fin s) F ≃ᵐ Matrix (Fin r) (Fin s) F :=
  Homeomorph.toMeasurableEquiv
    { toFun := fun X => A.val * X
      invFun := fun X => (A⁻¹ : Langlands.GeneralLinear r F).val * X
      left_inv := fun X => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun X => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }

theorem mulLeftMeasurableEquiv_apply {r : ℕ} (A : Langlands.GeneralLinear r F)
    (s : ℕ) (X : Matrix (Fin r) (Fin s) F) :
    mulLeftMeasurableEquiv F A s X = A.val * X := rfl

/-- Left multiplication by `A` scales the rectangular measure by `|det A|^(-s)`. -/
theorem map_mulLeftMeasurableEquiv (ν : AdditiveHaarMeasure F) {r : ℕ}
    (A : Langlands.GeneralLinear r F) (s : ℕ) :
    (rectangularMeasure ν r s).map (mulLeftMeasurableEquiv F A s) =
      (((⟨⟩ : LocalFieldData F).determinantNorm r A : ℝ≥0) ^ s)⁻¹ •
        rectangularMeasure ν r s := by
  have h := padicRectangularHaarScaling F (⟨⟩ : LocalFieldData F) r s
    (rectangularMeasure ν r s) A 1
  simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, one_pow, div_one] at h
  exact h

/-- The lower-left substitution `C = -((d⁻¹)ᵀ xᵀ)` multiplies the rectangular measure
by `|det d|^(n₀)`. -/
theorem integral_comp_lowerLeft {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : AdditiveHaarMeasure F) {n0 n1 : ℕ} (d : Langlands.GeneralLinear n1 F)
    (G : Matrix (Fin n1) (Fin n0) F → E) :
    ∫ x, G (-((GeneralLinear.inverseTranspose n1 F d).val * x.transpose))
        ∂rectangularMeasure ν n0 n1 =
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det ^ n0) •
        ∫ C, G C ∂rectangularMeasure ν n1 n0 := by
  set A : Langlands.GeneralLinear n1 F :=
    -GeneralLinear.inverseTranspose n1 F d with hAdef
  have hA : ∀ y, mulLeftMeasurableEquiv F A n0 y =
      -((GeneralLinear.inverseTranspose n1 F d).val * y) := fun y => by
    rw [mulLeftMeasurableEquiv_apply, hAdef, Units.val_neg, Matrix.neg_mul]
  have hdet : (((⟨⟩ : LocalFieldData F).determinantNorm n1 A : ℝ≥0) : ℝ) =
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det)⁻¹ := by
    rw [Langlands.LocalFieldData.determinantNorm_coe]
    change normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
      ((GeneralLinear.determinant A : Fˣ) : F) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, hAdef, Units.val_neg, Matrix.det_neg,
      AbsoluteValue.map_mul, AbsoluteValue.map_pow, AbsoluteValue.map_neg,
      AbsoluteValue.map_one, one_pow, one_mul, abv_det_inverseTranspose]
  calc ∫ x, G (-((GeneralLinear.inverseTranspose n1 F d).val * x.transpose))
        ∂rectangularMeasure ν n0 n1
      = ∫ x, (fun y => G (mulLeftMeasurableEquiv F A n0 y))
          (transposeMeasurableEquiv n0 n1 x) ∂rectangularMeasure ν n0 n1 := by
        simp only [hA]
        rfl
    _ = ∫ y, G (mulLeftMeasurableEquiv F A n0 y) ∂rectangularMeasure ν n1 n0 :=
        (measurePreserving_transpose_rectangularMeasure ν n0 n1).integral_comp'
          (fun y => G (mulLeftMeasurableEquiv F A n0 y))
    _ = ∫ C, G C ∂((rectangularMeasure ν n1 n0).map (mulLeftMeasurableEquiv F A n0)) :=
        (integral_map_equiv _ G).symm
    _ = _ := by
        rw [map_mulLeftMeasurableEquiv, integral_smul_nnreal_measure, NNReal.smul_def]
        congr 1
        rw [NNReal.coe_inv, NNReal.coe_pow, hdet, inv_pow, inv_inv]

/-- Integrability is preserved by the lower-left substitution. -/
theorem integrable_comp_lowerLeft {E : Type*} [NormedAddCommGroup E]
    (ν : AdditiveHaarMeasure F) {n0 n1 : ℕ} (d : Langlands.GeneralLinear n1 F)
    {G : Matrix (Fin n1) (Fin n0) F → E}
    (hG : Integrable G (rectangularMeasure ν n1 n0)) :
    Integrable (fun x => G (-((GeneralLinear.inverseTranspose n1 F d).val *
      x.transpose))) (rectangularMeasure ν n0 n1) := by
  set A : Langlands.GeneralLinear n1 F :=
    -GeneralLinear.inverseTranspose n1 F d with hAdef
  have hA : ∀ y, mulLeftMeasurableEquiv F A n0 y =
      -((GeneralLinear.inverseTranspose n1 F d).val * y) := fun y => by
    rw [mulLeftMeasurableEquiv_apply, hAdef, Units.val_neg, Matrix.neg_mul]
  have h1 : Integrable G ((rectangularMeasure ν n1 n0).map (mulLeftMeasurableEquiv F A n0)) := by
    rw [map_mulLeftMeasurableEquiv]
    exact hG.smul_measure_nnreal
  have h2 := (integrable_map_equiv _ G).mp h1
  have h3 := ((measurePreserving_transpose_rectangularMeasure ν n0 n1).integrable_comp_emb
    (transposeMeasurableEquiv n0 n1).measurableEmbedding).mpr h2
  convert h3 using 2 with x
  simp only [Function.comp_apply, hA]
  rfl

section DualParabolic

variable {n0 n1 N : ℕ} (e : Fin n0 ⊕ Fin n1 ≃ Fin N)

/-- The transformed integrand `Φ ([[a, a x], [0, d]]⁻ᵀ) u₀(a) u₁(d)` in the coordinates
`((a, d), x)`, written through the block form
`[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]` of the inverse transpose. -/
def dualParabolicIntegrand (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F))
    (u0 : Langlands.GeneralLinear n0 F → ℂ)
    (u1 : Langlands.GeneralLinear n1 F → ℂ)
    (z : (Langlands.GeneralLinear n0 F × Langlands.GeneralLinear n1 F) ×
      Matrix (Fin n0) (Fin n1) F) : ℂ :=
  Φ (blockMatrix e (GeneralLinear.inverseTranspose n0 F z.1.1).val 0
      (-((GeneralLinear.inverseTranspose n1 F z.1.2).val * z.2.transpose))
      (GeneralLinear.inverseTranspose n1 F z.1.2).val) * u0 z.1.1 * u1 z.1.2

theorem measurable_inverseTranspose_val (n : ℕ) :
    Measurable fun a : Langlands.GeneralLinear n F =>
      (GeneralLinear.inverseTranspose n F a).val :=
  (Units.continuous_val.comp (GeneralLinear.continuous_inverseTranspose n F)).measurable

/-- The transformed integrand is a.e. strongly measurable for every product measure
for which the two Levi weights are. -/
theorem aestronglyMeasurable_dualParabolicIntegrand (ν : AdditiveHaarMeasure F)
    {μ0 : Measure (Langlands.GeneralLinear n0 F)}
    {μ1 : Measure (Langlands.GeneralLinear n1 F)} [SFinite μ0] [SFinite μ1]
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F))
    {u0 : Langlands.GeneralLinear n0 F → ℂ}
    {u1 : Langlands.GeneralLinear n1 F → ℂ}
    (hu0m : AEStronglyMeasurable u0 μ0) (hu1m : AEStronglyMeasurable u1 μ1) :
    AEStronglyMeasurable (dualParabolicIntegrand F e Φ u0 u1)
      ((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) := by
  have hblk : Continuous fun w : Matrix (Fin n0) (Fin n0) F ×
      Matrix (Fin n1) (Fin n0) F × Matrix (Fin n1) (Fin n1) F =>
        blockMatrix e w.1 0 w.2.1 w.2.2 :=
    (continuous_fst.matrix_fromBlocks continuous_const (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).matrix_reindex e e
  have hT0 := measurable_inverseTranspose_val F n0
  have hT1 := measurable_inverseTranspose_val F n1
  have hψ : Measurable fun z : (Langlands.GeneralLinear n0 F ×
      Langlands.GeneralLinear n1 F) × Matrix (Fin n0) (Fin n1) F =>
        ((GeneralLinear.inverseTranspose n0 F z.1.1).val,
          -((GeneralLinear.inverseTranspose n1 F z.1.2).val * z.2.transpose),
          (GeneralLinear.inverseTranspose n1 F z.1.2).val) :=
    (hT0.comp (measurable_fst.comp measurable_fst)).prodMk
      ((((continuous_fst.matrix_mul continuous_snd.matrix_transpose).neg).measurable.comp
        ((hT1.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).prodMk
        (hT1.comp (measurable_snd.comp measurable_fst)))
  have hΦ := ((Φ.continuous.comp hblk).stronglyMeasurable.comp_measurable hψ).aestronglyMeasurable
    (μ := (μ0.prod μ1).prod (rectangularMeasure ν n0 n1))
  exact (hΦ.mul hu0m.comp_fst.comp_fst).mul hu1m.comp_snd.comp_fst

/-- **Dual parabolic reduction.** Suppose the lower-left partial integral of `Φ` is a
finite sum of tensor products `∑ₖ αₖ(x) βₖ(y)`, and that `a ↦ Ψ((a⁻¹)ᵀ) u₀(a)` and
`d ↦ Ψ((d⁻¹)ᵀ) u₁(d) |det d|^(n₀)` are integrable for every Schwartz–Bruhat `Ψ`.
Then the transformed integrand is integrable on `(GL_{n₀} × GL_{n₁}) × M_{n₀×n₁}`, and its
integral is `∑ₖ (∫ αₖ((a⁻¹)ᵀ) u₀(a) da) (∫ βₖ((d⁻¹)ᵀ) u₁(d) |det d|^(n₀) dd)`. -/
theorem integrable_integral_dualParabolicIntegrand (ν : AdditiveHaarMeasure F)
    {μ0 : Measure (Langlands.GeneralLinear n0 F)}
    {μ1 : Measure (Langlands.GeneralLinear n1 F)} [SFinite μ0] [SFinite μ1]
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F))
    {u0 : Langlands.GeneralLinear n0 F → ℂ}
    {u1 : Langlands.GeneralLinear n1 F → ℂ}
    (hu0m : AEStronglyMeasurable u0 μ0) (hu1m : AEStronglyMeasurable u1 μ1)
    (hu0 : ∀ Ψ : SchwartzBruhat (Matrix (Fin n0) (Fin n0) F),
      Integrable (fun a => Ψ (GeneralLinear.inverseTranspose n0 F a).val * u0 a) μ0)
    (hu1 : ∀ Ψ : SchwartzBruhat (Matrix (Fin n1) (Fin n1) F),
      Integrable (fun d => Ψ (GeneralLinear.inverseTranspose n1 F d).val *
        (u1 d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^ n0)) μ1)
    {ι : Type*} (S : Finset ι) (α : ι → SchwartzBruhat (Matrix (Fin n0) (Fin n0) F))
    (β : ι → SchwartzBruhat (Matrix (Fin n1) (Fin n1) F))
    (hpart : ∀ x y, ∫ C, Φ (blockMatrix e x 0 C y) ∂rectangularMeasure ν n1 n0 =
      ∑ k ∈ S, α k x * β k y) :
    Integrable (dualParabolicIntegrand F e Φ u0 u1)
        ((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) ∧
      ∫ z, dualParabolicIntegrand F e Φ u0 u1 z
          ∂((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) =
        ∑ k ∈ S, (∫ a, α k (GeneralLinear.inverseTranspose n0 F a).val * u0 a ∂μ0) *
          ∫ d, β k (GeneralLinear.inverseTranspose n1 F d).val *
            (u1 d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^ n0)
            ∂μ1 := by
  obtain ⟨M, bA, bC, bD, hM⟩ := exists_blockMatrix_majorant e Φ
  let G : (Langlands.GeneralLinear n0 F × Langlands.GeneralLinear n1 F) →
      Matrix (Fin n1) (Fin n0) F → ℂ := fun ad C =>
    Φ (blockMatrix e (GeneralLinear.inverseTranspose n0 F ad.1).val 0 C
      (GeneralLinear.inverseTranspose n1 F ad.2).val)
  have hbC : Integrable (fun C => ‖bC C‖) (rectangularMeasure ν n1 n0) :=
    (bC.continuous.integrable_of_hasCompactSupport bC.hasCompactSupport).norm
  have hG : ∀ ad, Integrable (G ad) (rectangularMeasure ν n1 n0) := fun ad =>
    Integrable.mono' (hbC.const_mul (M * (‖bA (GeneralLinear.inverseTranspose n0 F
        ad.1).val‖ * ‖bD (GeneralLinear.inverseTranspose n1 F ad.2).val‖)))
      (Φ.continuous.comp ((continuous_const.matrix_fromBlocks continuous_const continuous_id
        continuous_const).matrix_reindex e e)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun C => (hM _ C _).trans_eq (by ring))
  have hGnorm : ∀ ad, ∫ C, ‖G ad C‖ ∂rectangularMeasure ν n1 n0 ≤
      M * (‖bA (GeneralLinear.inverseTranspose n0 F ad.1).val‖ *
        ‖bD (GeneralLinear.inverseTranspose n1 F ad.2).val‖) *
        ∫ C, ‖bC C‖ ∂rectangularMeasure ν n1 n0 := fun ad => by
    rw [← integral_const_mul]
    exact integral_mono (hG ad).norm (hbC.const_mul _) fun C => (hM _ C _).trans_eq (by ring)
  have hfib : ∀ ad x, dualParabolicIntegrand F e Φ u0 u1 (ad, x) =
      G ad (-((GeneralLinear.inverseTranspose n1 F ad.2).val * x.transpose)) *
        u0 ad.1 * u1 ad.2 := fun _ _ => rfl
  have hfibInt : ∀ ad, Integrable (fun x => dualParabolicIntegrand F e Φ u0 u1 (ad, x))
      (rectangularMeasure ν n0 n1) := fun ad => by
    simp only [hfib]
    exact ((integrable_comp_lowerLeft F ν ad.2 (hG ad)).mul_const _).mul_const _
  have hfibNorm : ∀ ad, ∫ x, ‖dualParabolicIntegrand F e Φ u0 u1 (ad, x)‖
      ∂rectangularMeasure ν n0 n1 =
        normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) ad.2.val.det ^ n0 *
          (∫ C, ‖G ad C‖ ∂rectangularMeasure ν n1 n0) * ‖u0 ad.1‖ * ‖u1 ad.2‖ := fun ad => by
    simp only [hfib, norm_mul]
    rw [integral_mul_const, integral_mul_const,
      integral_comp_lowerLeft F ν ad.2 (fun C => ‖G ad C‖), smul_eq_mul]
  have hfibVal : ∀ ad, ∫ x, dualParabolicIntegrand F e Φ u0 u1 (ad, x)
      ∂rectangularMeasure ν n0 n1 =
        ∑ k ∈ S, (α k (GeneralLinear.inverseTranspose n0 F ad.1).val * u0 ad.1) *
          (β k (GeneralLinear.inverseTranspose n1 F ad.2).val *
            (u1 ad.2 *
              (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) ad.2.val.det : ℂ) ^ n0)) :=
    fun ad => by
      simp only [hfib]
      rw [integral_mul_const, integral_mul_const, integral_comp_lowerLeft F ν ad.2 (G ad)]
      simp only [G, hpart, Complex.real_smul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
  have hQm := aestronglyMeasurable_dualParabolicIntegrand F e ν Φ hu0m hu1m
  have hint : Integrable (dualParabolicIntegrand F e Φ u0 u1)
      ((μ0.prod μ1).prod (rectangularMeasure ν n0 n1)) := by
    rw [integrable_prod_iff hQm]
    refine ⟨Filter.Eventually.of_forall hfibInt, ?_⟩
    refine Integrable.mono'
      (((hu0 bA).norm.mul_prod (hu1 bD).norm).const_mul
        (M * ∫ C, ‖bC C‖ ∂rectangularMeasure ν n1 n0))
      hQm.norm.integral_prod_right' (Filter.Eventually.of_forall fun ad => ?_)
    have h0 : 0 ≤ normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) ad.2.val.det ^ n0 :=
      pow_nonneg (AbsoluteValue.nonneg _ _) n0
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hfibNorm]
    have h1 : 0 ≤ normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) ad.2.val.det :=
      AbsoluteValue.nonneg _ _
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
    calc _ ≤ normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) ad.2.val.det ^ n0 *
          (M * (‖bA (GeneralLinear.inverseTranspose n0 F ad.1).val‖ *
            ‖bD (GeneralLinear.inverseTranspose n1 F ad.2).val‖) *
            ∫ C, ‖bC C‖ ∂rectangularMeasure ν n1 n0) * ‖u0 ad.1‖ * ‖u1 ad.2‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hGnorm ad) h0) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  simp_rw [hfibVal]
  rw [integral_finsetSum _ fun k _ => (hu0 (α k)).mul_prod (hu1 (β k))]
  exact Finset.sum_congr rfl fun k _ => integral_prod_mul
    (fun a => α k (GeneralLinear.inverseTranspose n0 F a).val * u0 a)
    (fun d => β k (GeneralLinear.inverseTranspose n1 F d).val *
      (u1 d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^ n0))

end DualParabolic

section LeviCoordinates

variable {m : Fin 2 → ℕ} {N : ℕ} (e : Fin (m 0 + 1) ⊕ Fin (m 1 + 1) ≃ Fin N)

/-- **Dual parabolic reduction in Levi coordinates.** Let `g (L, x)` be the matrix
`[[L₀, L₀ x], [0, L₁]]` of the upper two-block parabolic, and integrate
`Φ ((g⁻¹)ᵀ) u₀(L₀) u₁(L₁)` against `(∏ᵢ μᵢ) × dx`. If the lower-left partial integral of
`Φ` is `∑ₖ αₖ(x) βₖ(y)`, the integrand is integrable and its integral is
`∑ₖ (∫ αₖ((a⁻¹)ᵀ) u₀(a) da) (∫ βₖ((d⁻¹)ᵀ) u₁(d) |det d|^(m₀+1) dd)`. -/
theorem integrable_integral_dualParabolic_levi (ν : AdditiveHaarMeasure F)
    (μ : ∀ i : Fin 2, Measure (Langlands.GeneralLinear (m i + 1) F))
    [∀ i, SigmaFinite (μ i)]
    (g : (∀ i : Fin 2, Langlands.GeneralLinear (m i + 1) F) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → Langlands.GeneralLinear N F)
    (hg : ∀ L x, (g (L, x)).val =
      Matrix.reindex e e (Matrix.fromBlocks (L 0).val ((L 0).val * x) 0 (L 1).val))
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) F))
    {u0 : Langlands.GeneralLinear (m 0 + 1) F → ℂ}
    {u1 : Langlands.GeneralLinear (m 1 + 1) F → ℂ}
    (hu0m : AEStronglyMeasurable u0 (μ 0)) (hu1m : AEStronglyMeasurable u1 (μ 1))
    (hu0 : ∀ Ψ : SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F),
      Integrable (fun a => Ψ (GeneralLinear.inverseTranspose (m 0 + 1) F a).val * u0 a)
        (μ 0))
    (hu1 : ∀ Ψ : SchwartzBruhat (Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F),
      Integrable (fun d => Ψ (GeneralLinear.inverseTranspose (m 1 + 1) F d).val *
        (u1 d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^ (m 0 + 1)))
        (μ 1))
    {ι : Type*} (S : Finset ι)
    (α : ι → SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F))
    (β : ι → SchwartzBruhat (Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F))
    (hpart : ∀ x y, ∫ C, Φ (blockMatrix e x 0 C y) ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1) =
      ∑ k ∈ S, α k x * β k y) :
    Integrable (fun z => Φ (GeneralLinear.inverseTranspose N F (g z)).val *
        (u0 (z.1 0) * u1 (z.1 1)))
        ((Measure.pi μ).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1))) ∧
      ∫ z, Φ (GeneralLinear.inverseTranspose N F (g z)).val * (u0 (z.1 0) * u1 (z.1 1))
          ∂((Measure.pi μ).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1))) =
        ∑ k ∈ S,
          (∫ a, α k (GeneralLinear.inverseTranspose (m 0 + 1) F a).val * u0 a ∂μ 0) *
          ∫ d, β k (GeneralLinear.inverseTranspose (m 1 + 1) F d).val *
            (u1 d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^
              (m 0 + 1)) ∂μ 1 := by
  let Θ := (MeasurableEquiv.piFinTwo fun i : Fin 2 =>
      Langlands.GeneralLinear (m i + 1) F).prodCongr
    (MeasurableEquiv.refl (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
  have hΘ : MeasurePreserving Θ ((Measure.pi μ).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1)))
      (((μ 0).prod (μ 1)).prod (rectangularMeasure ν (m 0 + 1) (m 1 + 1))) :=
    (measurePreserving_piFinTwo μ).prod (MeasurePreserving.id _)
  have hfun : (fun z => Φ (GeneralLinear.inverseTranspose N F (g z)).val *
      (u0 (z.1 0) * u1 (z.1 1))) = dualParabolicIntegrand F e Φ u0 u1 ∘ Θ := by
    funext z
    obtain ⟨L, x⟩ := z
    change _ = Φ (blockMatrix e _ 0 _ _) * u0 (L 0) * u1 (L 1)
    rw [inverseTranspose_val_of_upperBlock e (g (L, x)) (L 0) (L 1) x (hg L x), mul_assoc]
    rfl
  obtain ⟨hint, hval⟩ := integrable_integral_dualParabolicIntegrand F e ν Φ hu0m hu1m hu0 hu1
    S α β hpart
  rw [hfun]
  exact ⟨(hΘ.integrable_comp_emb Θ.measurableEmbedding).mpr hint,
    (hΘ.integral_comp' (dualParabolicIntegrand F e Φ u0 u1)).trans hval⟩

end LeviCoordinates

section CompactTranslate

/-- **Dual compact step.** If the two-sided translate `x ↦ Φ (A x B)` by matrices of
normalized determinant one decomposes as `∑ₗ cₗ Φₗ`, then the Fourier transform of `Φ` at
the inverse transpose of `A g B` decomposes with the same coefficients as
`∑ₗ cₗ (FΦₗ)((g⁻¹)ᵀ)`. -/
theorem rectangularFourierEquiv_inverseTranspose_translate
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) {n : ℕ} (A B : Langlands.GeneralLinear n F)
    (hA : (⟨⟩ : LocalFieldData F).determinantNorm n A = 1)
    (hB : (⟨⟩ : LocalFieldData F).determinantNorm n B = 1)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) F)) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (Φs : ι → SchwartzBruhat (Matrix (Fin n) (Fin n) F))
    (hdec : ∀ x, Φ (A.val * x * B.val) = ∑ l ∈ S, c l * Φs l x)
    (g : Langlands.GeneralLinear n F) :
    rectangularFourierEquiv ψ ν n n hsd Φ
        (GeneralLinear.inverseTranspose n F (A * (g * B))).val =
      ∑ l ∈ S, c l * rectangularFourierEquiv ψ ν n n hsd (Φs l)
        (GeneralLinear.inverseTranspose n F g).val := by
  rw [← mul_assoc, map_mul, map_mul, Units.val_mul, Units.val_mul]
  simp only [rectangularFourierEquiv_apply]
  exact rectangularFourierIntegral_translate_decomposition (⟨⟩ : LocalFieldData F) ψ ν A B
    hA hB Φ S c Φs hdec _

/-- The dual compact step for two elements of a compact subgroup of `GL_n`. -/
theorem rectangularFourierEquiv_inverseTranspose_translate_of_mem
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) {n : ℕ} (K : Subgroup (Langlands.GeneralLinear n F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear n F)))
    {A B : Langlands.GeneralLinear n F} (hA : A ∈ K) (hB : B ∈ K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin n) F)) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (Φs : ι → SchwartzBruhat (Matrix (Fin n) (Fin n) F))
    (hdec : ∀ x, Φ (A.val * x * B.val) = ∑ l ∈ S, c l * Φs l x)
    (g : Langlands.GeneralLinear n F) :
    rectangularFourierEquiv ψ ν n n hsd Φ
        (GeneralLinear.inverseTranspose n F (A * (g * B))).val =
      ∑ l ∈ S, c l * rectangularFourierEquiv ψ ν n n hsd (Φs l)
        (GeneralLinear.inverseTranspose n F g).val :=
  rectangularFourierEquiv_inverseTranspose_translate F ψ ν hsd A B
    ((⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_mem_compact n K hK A hA)
    ((⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_mem_compact n K hK B hB) Φ S c Φs hdec g

end CompactTranslate

end Padic

end Langlands.AllField.GodementJacquet
