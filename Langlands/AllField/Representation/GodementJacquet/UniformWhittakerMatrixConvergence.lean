import Langlands.Representation.GodementJacquet.UniformWhittakerMatrixConvergence
import Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.GodementJacquet.UniformWhittakerSliceBound
import Langlands.AllField.Representation.GodementJacquet.WhittakerModelRationality
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement
import Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof
/-!
# Common matrix convergence on actual coefficient models

A uniform finite-function Mellin threshold and the fixed unipotent-slice
exponents give one matrix-convergence half-plane before all model functions
and full-matrix tests. Finite smooth-dual averaging transfers that bound to
the actual bi-smooth coefficient span. The uniform Mellin premise is explicit.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus.Padic hiding HasTorusExpansion IsWhittakerLike borelModulus borelModulus_mul borelModulus_pos boxTest boxTest_apply_of_le continuous_borelModulus continuous_normalizedAbs_prod continuous_torusWeight enorm_torusWeight exists_common_glModel_halfPlane exists_common_matrix_halfPlane exists_common_modelMatrix_halfPlane exists_modelMatrixConvergenceBound exists_slice_bound exists_uniform_slice_bound glModelFunction_isWhittakerLike glModel_matrixConvergesOnRight glModel_shifted_of_converges initTail integralK integral_iwasawa integral_unipotent_matrixIntegrand isClopen_normBox isCompact_normBox isFiniteFunction_torusWeight isFiniteFunction_twistedCharacter iwasawaReductionBorelSpace iwasawaReductionLocalField iwasawaReductionMeasurableSpace iwasawaReductionTopology iwasawaReductionUnipotentBorelSpace iwasawaReductionUnipotentMeasurableSpace iwasawaReductionUnitsBorelSpace iwasawaReductionUnitsMeasurableSpace iwasawaReductionValuativeRel lintegral_iwasawa lintegral_torus_lt_top lintegral_torus_lt_top_of_uniform_terms lintegral_unipotent_matrixIntegrand matrixConvergenceBorelSpace matrixConvergenceLocalField matrixConvergenceMeasurableSpace matrixConvergenceTopology matrixConvergenceUnipotentBorelSpace matrixConvergenceUnipotentMeasurableSpace matrixConvergenceUnitsBorelSpace matrixConvergenceUnitsMeasurableSpace matrixConvergenceValuativeRel matrixIntegrand_iwasawa matrixIntegrand_mul_right matrixRationalityBorelSpace matrixRationalityLocalField matrixRationalityMeasurableSpace matrixRationalityTopology matrixRationalityUnipotentBorelSpace matrixRationalityUnipotentMeasurableSpace matrixRationalityUnitsBorelSpace matrixRationalityUnitsMeasurableSpace matrixRationalityValuativeRel measurable_matrixIntegrand modelCoefficient_converges_of_modelFunctions modelMatrixConvergenceBound modelMatrixConvergenceBound_spec modelRationalityLocalField modelRationalityTopology modelRationalityValuativeRel modelWhittakerRationality normBox normalizedAbs_det_integralK normalizedAbs_prod_mul normalizedAbs_prod_pos normalizedAbs_units_pos ratios sliceBoundBorelSpace sliceBoundLocalField sliceBoundMeasurableSpace sliceBoundTopology sliceBoundUnipotentBorelSpace sliceBoundUnipotentMeasurableSpace sliceBoundValuativeRel sliceExponents sliceTest sliceTest_apply torusIntegrand torusIntegrand_tailProd torusMellin torusMellinLocalField torusMellinTopology torusMellinUnitsBorelSpace torusMellinUnitsMeasurableSpace torusMellinValuativeRel torusMonomial torusMonomial_nonneg torusWeight torusWeight_mul twistedCharacter uniformMatrixBorelSpace uniformMatrixLocalField uniformMatrixMeasurableSpace uniformMatrixModelAddCommGroup uniformMatrixTopology uniformMatrixUnipotentBorelSpace uniformMatrixUnipotentMeasurableSpace uniformMatrixUnitsBorelSpace uniformMatrixUnitsMeasurableSpace uniformMatrixValuativeRel uniformSliceLocalField uniformSliceTopology uniformSliceUnipotentBorelSpace uniformSliceUnipotentMeasurableSpace uniformSliceValuativeRel uniform_torusMellin unipotent_volume_bound_uniform whittakerModelComparison_of_asymptotics
open Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice rootCoordinateChange setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable unequalRankIwasawaSupport unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators ENNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance uniformMatrixUnitsMeasurableSpace : MeasurableSpace Fˣ := borel _
local instance uniformMatrixUnitsBorelSpace : BorelSpace Fˣ := ⟨rfl⟩
local instance uniformMatrixMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance uniformMatrixBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance uniformMatrixUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance uniformMatrixUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

local instance uniformMatrixModelAddCommGroup
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- Tail-product change of variables preserves a single half-plane chosen
before every pair of additive test functions. -/
theorem uniform_torusMellin
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (X : Finset (((Fin (n + 1) → Fˣ) → ℂ)))
    (hX : ∀ η ∈ X, IsFiniteFunction η) :
    ∃ c : ℝ, ∀ η ∈ X, ∀ (φ : SchwartzBruhat (Fin n → F))
      (J : SchwartzBruhat (Fin (n + 1) → F)),
      ∀ s : ℂ, c < s.re → Integrable (torusIntegrand F φ J η s)
        (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) := by
  classical
  have : SecondCountableTopology F :=
    Langlands.LocalFieldData.secondCountableTopology (⟨⟩ : LocalFieldData F)
  have : SecondCountableTopology Fˣ := Units.isEmbedding_val₀.secondCountableTopology
  let pull := fun η : (Fin (n + 1) → Fˣ) → ℂ =>
    η ∘ (tailProdEquiv (G := Fˣ) (n := n)).toMonoidHom
  obtain ⟨c, hc⟩ := hU F (⟨⟩ : LocalFieldData F) (n + 1)
    (fun i => (i : ℕ) + 1) (fun _ => Nat.succ_pos _) (X.image pull) (by
      intro η hη
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp hη
      exact (hX ξ hξ).comp _ continuous_tailProd)
  refine ⟨c, ?_⟩
  intro η hη φ J s hs
  have hmp := measurePreserving_tailProd (E := F) (n := n)
  have hme : MeasurableEmbedding (tailProd : (Fin (n + 1) → Fˣ) → _) :=
    (tailProdHomeomorph (G := Fˣ) (n := n)).toHomeomorph.measurableEmbedding
  rw [← hmp.integrable_comp_emb hme]
  change Integrable (fun x => torusIntegrand F φ J η s (tailProd x)) _
  simpa [torusIntegrand_tailProd, pull, tailProdEquiv] using
    hc (pull η) (Finset.mem_image.mpr ⟨η, hη, rfl⟩) (initTail F φ J) s hs

/-- The unipotent/torus estimate at a fixed parameter, using the common
finite family and fixed slice exponents. -/
theorem lintegral_torus_lt_top_of_uniform_terms
    {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F) {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralK F n)
    (X : Finset (((Fin (n + 1) → Fˣ) → ℂ)))
    (φ : ((Fin (n + 1) → Fˣ) → ℂ) → SchwartzBruhat (Fin n → F))
    (hφ : ∀ a, W (Iwasawa.diagonalUnits a * k) =
      ∑ χ ∈ X, φ χ (ratios F a) * χ a)
    (s : ℂ)
    (hterms : ∀ (J : SchwartzBruhat (Fin (n + 1) → F)), ∀ χ ∈ X,
      Integrable (torusIntegrand F (φ χ) J (χ * torusWeight F (sliceExponents F n)) s)
        (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F)) :
    ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) < ⊤ := by
  obtain ⟨B, ρ, hρ, hslice⟩ := exists_uniform_slice_bound F Φ k
  let e := sliceExponents F n
  let J := boxTest F n hρ
  have hint := hterms J
  have hpt : ∀ a : Fin (n + 1) → Fˣ,
      ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n ≤
        ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
    intro a
    rw [lintegral_unipotent_matrixIntegrand F hW.equivariant Φ s a hk]
    have hsum : W (Iwasawa.diagonalUnits a * k) *
        (J (fun i => (a i : F)) * torusWeight F e a *
          (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s) =
        ∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a := by
      rw [show W (Iwasawa.diagonalUnits a * k) = ∑ χ ∈ X, φ χ (ratios F a) * χ a from hφ a,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun χ _ => ?_
      simp only [torusIntegrand, Pi.mul_apply]
      ring
    calc ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s‖ₑ *
          ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ
            ∂unipotentHaar F n)
        ≤ ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s‖ₑ *
          (ENNReal.ofReal B * ENNReal.ofReal (torusMonomial F e a) *
            ‖J (fun i => (a i : F))‖ₑ)) := by
          gcongr
          exact hslice a
      _ = ENNReal.ofReal B * ‖W (Iwasawa.diagonalUnits a * k) *
          (J (fun i => (a i : F)) * torusWeight F e a *
            (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^
              s)‖ₑ := by
          simp only [enorm_mul]
          rw [enorm_torusWeight]
          ring
      _ = ENNReal.ofReal B *
          ‖∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          rw [hsum]
      _ ≤ ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          gcongr
          exact enorm_sum_le _ _
  calc ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F)
      ≤ ∫⁻ a, ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal B * ∑ χ ∈ X, ∫⁻ a, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun χ hχ => (hint χ hχ).aestronglyMeasurable.enorm]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun χ hχ =>
        hasFiniteIntegral_iff_enorm.1 (hint χ hχ).hasFiniteIntegral)

/-- One fixed finite torus family gives one convergence threshold for all
Whittaker-like functions with expansions in that family and all matrix tests. -/
theorem exists_common_matrix_halfPlane
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (X : Finset (((Fin (n + 1) → Fˣ) → ℂ)))
    (hX : ∀ χ ∈ X, IsFiniteFunction χ) :
    ∃ c : ℝ, ∀ (ψ : UnitaryAdditiveCharacter F)
      (W : Langlands.GeneralLinear (n + 1) F → ℂ),
      IsWhittakerLike F ψ W →
      (∀ k : Langlands.GeneralLinear (n + 1) F,
        ∃ φ : ((Fin (n + 1) → Fˣ) → ℂ) → SchwartzBruhat (Fin n → F),
          ∀ a, W (Iwasawa.diagonalUnits a * k) =
            ∑ χ ∈ X, φ χ (ratios F a) * χ a) →
      ∀ (Φ : MatrixTestFunction n F) (s : ℂ), c < s.re →
        Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s W := by
  classical
  let twist := fun χ : (Fin (n + 1) → Fˣ) → ℂ =>
    χ * torusWeight F (sliceExponents F n)
  obtain ⟨c, hc⟩ := uniform_torusMellin F hU (X.image twist) (by
    intro η hη
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hη
    exact (hX χ hχ).mul (isFiniteFunction_torusWeight F _))
  refine ⟨c, ?_⟩
  intro ψ W hW hexp Φ s hs
  have htorus : ∀ k ∈ integralK F n,
      ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) < ⊤ := by
    intro k hk
    obtain ⟨φ, hφ⟩ := hexp k
    exact lintegral_torus_lt_top_of_uniform_terms F hW Φ hk X φ hφ s
      (fun J χ hχ => hc (twist χ) (Finset.mem_image.mpr ⟨χ, hχ, rfl⟩) (φ χ) J s hs)
  obtain ⟨K₀, S, hK₀K, hSK, hinv, hlin, -⟩ := Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.IsWhittakerLike.exists_cosetSum F hW Φ
  have hmeas := measurable_matrixIntegrand F hW.continuous Φ s
  change Integrable (Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W) (generalLinearHaar F n)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_iwasawa F _ hmeas.enorm,
    hlin (fun k => ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F))
      fun k _ k₀ hk₀ => ?_]
  · refine ENNReal.sum_lt_top.2 fun k hk => ENNReal.mul_lt_top ?_ (htorus k (hSK hk))
    exact (measure_mono fun x hx => hK₀K hx).trans_lt
      ((generalLinearHaar_integralSubgroup F n).trans_lt ENNReal.one_lt_top)
  · refine lintegral_congr fun a => ?_
    congr 1
    refine lintegral_congr fun u => ?_
    rw [← mul_assoc, hinv s _ k₀ hk₀]

/-- A common shifted half-plane precedes every functional, model vector and
matrix test, using a fixed coefficient-torus expansion. -/
theorem exists_common_glModel_halfPlane
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ) :
    ∃ c : ℝ, ∀ (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F)
      (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) (s : ℂ), c < s.re →
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n)
        (glModelFunction ψ n σ ℓ w) := by
  obtain ⟨X, hX, hφ⟩ := hexp
  obtain ⟨c, hc⟩ := exists_common_matrix_halfPlane F hU X hX
  refine ⟨c - (jpssShift n).re, ?_⟩
  intro ℓ Φ w s hs
  refine hc ψ (glModelFunction ψ n σ ℓ w)
    (glModelFunction_isWhittakerLike F ψ σ hσ ⟨X, hX, hφ⟩ ℓ w) ?_ Φ _ ?_
  · intro k
    obtain ⟨φ, hφ'⟩ := hφ ℓ (glModelRepresentation ψ n σ ℓ k w)
    exact ⟨φ, hφ'⟩
  · rw [Complex.add_re]
    linarith

/-- Common convergence for model functions transfers to an individual actual
smooth coefficient at the same parameter. -/
theorem modelCoefficient_converges_of_modelFunctions
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ n σ)
    (Φ : MatrixTestFunction n F)
    (Λ : SmoothDual (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ))
    (w : smoothVectors (glModelRepresentation ψ n σ ℓ)) (s : ℂ)
    (hconv : ∀ (Ψ : MatrixTestFunction n F)
      (v : (glCoefficientModel ψ n σ ℓ).toSubmodule),
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Ψ s (glModelFunction ψ n σ ℓ v)) :
    Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s
      (GodementJacquet.biSmoothCoefficient (glModelRepresentation ψ n σ ℓ) Λ w) := by
  obtain ⟨K, -, hK⟩ := Langlands.AllField.GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨L, hL, hLK, t, c, hc⟩ := Langlands.AllField.GodementJacquet.Padic.exists_eq_sum_modelPointAverage
    F ψ σ hσ.1 ℓ (Langlands.AllField.GodementJacquet.Padic.glModel_isAdmissible F ψ σ ℓ hσ) Λ K
  exact (Langlands.AllField.GodementJacquet.Padic.matrixIntegral_sum_modelPointAverage F ψ σ hσ.1 ℓ
    Φ L hL (fun k hk => hK k (hLK hk)) t c w.val
    (GodementJacquet.biSmoothCoefficient (glModelRepresentation ψ n σ ℓ) Λ w)
    (fun g => hc _) s (fun h _ => hconv _ _)).1

/-- One common half-plane for every actual bi-smooth coefficient of every
coefficient model, including reducible originals and the zero functional. -/
theorem exists_common_modelMatrix_halfPlane
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ) :
    ∃ c : ℝ, ∀ (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F)
      (f : GodementJacquet.biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ))
      (s : ℂ), c < s.re →
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n) f.val := by
  obtain ⟨c, hc⟩ := exists_common_glModel_halfPlane F hU ψ σ hσ hexp
  refine ⟨c, ?_⟩
  intro ℓ Φ f s hs
  apply GodementJacquet.matrixConverges_of_mem_span (f := f.val) _ f.property
  rintro g ⟨Λ, w, rfl⟩
  exact modelCoefficient_converges_of_modelFunctions F ψ σ hσ ℓ Φ Λ w _
    (fun Ψ v => hc ℓ Ψ v s hs)

/-- Full Whittaker type supplies the fixed expansion through the published
asymptotic proof. Only uniform Mellin convergence remains an explicit premise. -/
theorem exists_modelMatrixConvergenceBound
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ c : ℝ, ∀ (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F)
      (f : GodementJacquet.biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ))
      (s : ℂ), c < s.re →
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n) f.val := by
  exact exists_common_modelMatrix_halfPlane F hU ψ σ hσ.1
    (modelAsymptoticTransfer whittakerTypeAsymptotic F (⟨⟩ : LocalFieldData F)
      n V σ ψ (standardCharacter ψ n) (Or.inl rfl) hσ)

/-- A common real convergence bound on all actual coefficient models of a
full Whittaker-type representation. The uniform Mellin premise is explicit. -/
def modelMatrixConvergenceBound
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) : ℝ :=
  Classical.choose (exists_modelMatrixConvergenceBound F hU ψ σ hσ)

/-- The chosen bound precedes the functional, full-matrix test, actual
bi-smooth coefficient and spectral parameter. -/
theorem modelMatrixConvergenceBound_spec
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F)
    (f : GodementJacquet.biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ))
    (s : ℂ) (hs : modelMatrixConvergenceBound F hU ψ σ hσ < s.re) :
    Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n) f.val :=
  Classical.choose_spec (exists_modelMatrixConvergenceBound F hU ψ σ hσ) ℓ Φ f s hs

/-- Common shifted matrix convergence on each actual coefficient-model
representation, under uniform finite-function Mellin convergence. -/
theorem glModel_matrixConvergesOnRight
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) (ℓ : glFunctionals ψ n σ) :
    GodementJacquet.MatrixConvergesOnRight
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n)
      (glModelRepresentation ψ n σ ℓ) :=
  ⟨modelMatrixConvergenceBound F hU ψ σ hσ,
    modelMatrixConvergenceBound_spec F hU ψ σ hσ ℓ⟩

end Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
