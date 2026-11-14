import Langlands.Representation.RankinSelberg.TwoBlockDominantCentralScalar
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding equalGammaMeasurable equalGammaTopology hasModelMinusOneScalar_of_jacquetRealization jacquetFunction_blockMinusOne leviEmbedding_blockMinusOne leviModulus_blockMinusOne scalarSection_blockMinusOne tensorContraction_blockMinusOne
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.LocalFactor
open Langlands.AllField.LocalFactor
open scoped NNReal

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalGammaMeasurable : MeasurableSpace F := borel _

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

section CentralScalar

variable (ψ : UnitaryAdditiveCharacter F)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (ζ : Fin 2 → ℂˣ)
  (hζ : ∀ i, HasModelMinusOneScalar (σ i) (ell i) (ζ i))

include hζ

theorem tensorContraction_blockMinusOne (v : PiTensorProduct ℂ W) :
    tensorContraction (fun i => (ell i).val)
        ((succBlockShape m h).blockTensor σ (fun _ => -1) v) =
      (∏ i, (ζ i : ℂ)) * tensorContraction (fun i => (ell i).val) v := by
  have hell (i : Fin 2) (v : W i) :
      (ell i).val (σ i (-1) v) = (ζ i : ℂ) * (ell i).val v := by
    have ht := hζ i (modelMap (σ i) (ell i) v) 1
    change (ell i).val (σ i ((-1) * 1) v) =
      (ζ i : ℂ) * (ell i).val (σ i 1 v) at ht
    simpa only [mul_one, map_one, Module.End.one_apply] using ht
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod,
      tensorContraction_tprod, tensorContraction_tprod, smul_eq_mul, smul_eq_mul,
      mul_left_comm, ← Finset.prod_mul_distrib]
    congr 2
    funext i
    exact hell i (v i)
  | add v v' hv hv' =>
    rw [map_add, map_add, hv, hv', map_add, mul_add]

omit ψ σ ell ζ hζ in
theorem leviEmbedding_blockMinusOne :
    (succBlockShape m h).leviEmbedding F (fun _ => -1) =
      (-1 : GeneralLinear (t + 1) F) := by
  let B := succBlockShape m h
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding F (fun _ => -1) (B.index i a) (B.index j b) = _
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same]
    change (-1 : GeneralLinear (B.size i) F).val a b =
      (-1 : GeneralLinear (t + 1) F).val (B.index i a) (B.index i b)
    simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply,
      (B.index i).injective.eq_iff]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij]
    have hne : B.index i a ≠ B.index j b := by
      intro heq
      have hh := B.indexEquiv.injective heq
      exact hij (congrArg Sigma.fst hh)
    change (0 : F) =
      (-1 : GeneralLinear (t + 1) F).val (B.index i a) (B.index j b)
    simp [hne]

omit ψ σ ell ζ hζ in
theorem leviModulus_blockMinusOne :
    (⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h) (fun _ => -1) = 1 := by
  let L : (succBlockShape m h).Levi F := fun _ => -1
  have hL : L * L = 1 := by
    funext i
    change (-1 : GeneralLinear (m i + 1) F) * (-1) = 1
    simp
  let q := (⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h) L
  have hq : q * q = 1 := by rw [← map_mul, hL, map_one]
  apply Units.ext
  apply NNReal.eq
  have he : (q : ℝ) * (q : ℝ) = 1 := by
    simpa only [Units.val_mul, NNReal.coe_mul, Units.val_one, NNReal.coe_one] using
      congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hq
  have hp : 0 ≤ (q : ℝ) := (q : ℝ≥0).coe_nonneg
  change (q : ℝ) = 1
  nlinarith

theorem scalarSection_blockMinusOne
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    scalarSection (fun i => (ell i).val) f ((-1) * g) 1 =
      (∏ i, (ζ i : ℂ)) * scalarSection (fun i => (ell i).val) f g 1 := by
  have hc := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced_covariant
    (succBlockShape m h) ((succBlockShape m h).blockTensor σ) f
    ((succBlockShape m h).oppositeLeviInParabolic F (fun _ => -1)) g
  have he : sectionEval F h σ f ((-1) * g) =
      (succBlockShape m h).blockTensor σ (fun _ => -1) (sectionEval F h σ f g) := by
    simpa only [BlockShape.oppositeLeviInParabolic_val,
      BlockShape.oppositeLeviProjection_section, leviEmbedding_blockMinusOne,
      leviModulus_blockMinusOne, Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
      Complex.ofReal_one, inv_one, one_smul] using hc
  rw [scalarSection_one, he, tensorContraction_blockMinusOne F h ψ σ ell ζ hζ,
    scalarSection_one]

theorem jacquetFunction_blockMinusOne
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F) :
    jacquetFunction ψ (fun i => (ell i).val) μR f ((-1) * g) =
      (∏ i, (ζ i : ℂ)) * jacquetFunction ψ (fun i => (ell i).val) μR f g := by
  simp only [jacquetFunction_def, integrand_def]
  have heq (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
      upperRadical h F x * ((-1) * g) =
        (-1) * (upperRadical h F x * g) := by simp
  simp_rw [heq, scalarSection_blockMinusOne F h ψ σ ell ζ hζ, mul_assoc]
  exact integral_const_mul _ _

theorem hasModelMinusOneScalar_of_jacquetRealization
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (J : glInverseFunctionals ψ t (inducedRep F h σ))
    (hJ : ∀ (f : Sections F h σ) (g : GeneralLinear (t + 1) F),
      J.val (inducedRep F h σ g f) =
        jacquetFunction ψ (fun i => (ell i).val) μR f g) :
    HasModelMinusOneScalar (inducedRep F h σ) J (∏ i, ζ i) := by
  intro U g
  obtain ⟨f, rfl⟩ := modelMap_surjective (inducedRep F h σ) J U
  change J.val (inducedRep F h σ ((-1) * g) f) =
    ((∏ i, ζ i : ℂˣ) : ℂ) * J.val (inducedRep F h σ g f)
  rw [hJ, hJ, jacquetFunction_blockMinusOne F h ψ σ ell ζ hζ]
  simp

end CentralScalar

end Langlands.AllField.RankinSelberg.DominantRankTransport
