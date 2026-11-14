import Langlands.Representation.GodementJacquet.WhittakerMatrixRationality
import Langlands.AllField.Representation.GodementJacquet.WhittakerIwasawaReduction
/-!
# Rationality of full-matrix Whittaker integrals

Given `FiniteFunctionMellinStatement` and convergence on a right half-plane,
the full-matrix integral `∫ Φ(g) W(g) |det g|^(s + t) dg` of a function `W`
with `IsWhittakerLike` has a rational continuation in `q^(-s)`. On a right
half-plane the integral is a finite linear combination of the torus integrals
of `WhittakerTorusMellin`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.RationalContinuationLinear
open scoped BigOperators ENNReal

universe uF

namespace Padic
open Langlands.GodementJacquet.WhittakerTorus.Padic hiding HasTorusExpansion IsWhittakerLike borelModulus borelModulus_mul borelModulus_pos continuous_borelModulus continuous_normalizedAbs_prod initTail integralK integral_iwasawa integral_unipotent_matrixIntegrand isFiniteFunction_twistedCharacter iwasawaReductionBorelSpace iwasawaReductionLocalField iwasawaReductionMeasurableSpace iwasawaReductionTopology iwasawaReductionUnipotentBorelSpace iwasawaReductionUnipotentMeasurableSpace iwasawaReductionUnitsBorelSpace iwasawaReductionUnitsMeasurableSpace iwasawaReductionValuativeRel lintegral_iwasawa lintegral_unipotent_matrixIntegrand matrixIntegrand_iwasawa matrixIntegrand_mul_right matrixRationalityBorelSpace matrixRationalityLocalField matrixRationalityMeasurableSpace matrixRationalityTopology matrixRationalityUnipotentBorelSpace matrixRationalityUnipotentMeasurableSpace matrixRationalityUnitsBorelSpace matrixRationalityUnitsMeasurableSpace matrixRationalityValuativeRel normalizedAbs_det_integralK normalizedAbs_prod_mul normalizedAbs_prod_pos normalizedAbs_units_pos ratios sliceTest sliceTest_apply torusIntegrand torusIntegrand_tailProd torusMellin torusMellinLocalField torusMellinTopology torusMellinUnitsBorelSpace torusMellinUnitsMeasurableSpace torusMellinValuativeRel twistedCharacter
open Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matrixRationalityUnitsMeasurableSpace : MeasurableSpace Fˣ := borel _
local instance matrixRationalityUnitsBorelSpace : BorelSpace Fˣ := ⟨rfl⟩
local instance matrixRationalityMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance matrixRationalityBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance matrixRationalityUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance matrixRationalityUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The normalized absolute value of a unit is positive. -/
theorem normalizedAbs_units_pos (x : Fˣ) :
    0 < (⟨⟩ : LocalFieldData F).normalizedAbs (x : F) :=
  (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos x.ne_zero

/-- `|∏ a_i|` is positive. -/
theorem normalizedAbs_prod_pos (a : Fin (n + 1) → Fˣ) :
    0 < (⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) :=
  (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos
    (Finset.prod_ne_zero_iff.2 fun i _ => (a i).ne_zero)

/-- `|∏ a_i|` is multiplicative in `a`. -/
theorem normalizedAbs_prod_mul (b a : Fin (n + 1) → Fˣ) :
    (⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, ((b * a) i : F)) =
      (⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (b i : F)) *
        (⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) := by
  change normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) _ =
    normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) _ *
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) _
  rw [← map_mul, ← Finset.prod_mul_distrib]
  simp only [Pi.mul_apply, Units.val_mul]

/-- `a ↦ |∏ a_i|` is continuous. -/
theorem continuous_normalizedAbs_prod :
    Continuous fun a : Fin (n + 1) → Fˣ =>
      (⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) :=
  (Langlands.LocalFieldData.continuous_normalizedAbs (⟨⟩ : LocalFieldData F)).comp
    (continuous_finsetProd _ fun i _ => Units.continuous_val.comp (continuous_apply i))

/-- The modulus `δ` is positive. -/
theorem borelModulus_pos (a : Fin (n + 1) → Fˣ) : 0 < borelModulus F a :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => normalizedAbs_units_pos F _

/-- The modulus `δ` is multiplicative. -/
theorem borelModulus_mul (b a : Fin (n + 1) → Fˣ) :
    borelModulus F (b * a) = borelModulus F b * borelModulus F a := by
  unfold borelModulus
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  change normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) _ =
    normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) _ *
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) _
  rw [← map_mul, ← Units.val_mul, Pi.mul_apply, Pi.mul_apply,
    mul_div_mul_comm (b i) (a i) (b j) (a j)]

/-- The modulus `δ` is continuous. -/
theorem continuous_borelModulus : Continuous (borelModulus F (n := n)) :=
  continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ =>
    (Langlands.LocalFieldData.continuous_normalizedAbs (⟨⟩ : LocalFieldData F)).comp
      (Units.continuous_val.comp ((continuous_apply i).div' (continuous_apply j)))

/-- The function `χ(a) δ(a)⁻¹ |∏ a_i|^t` on the torus. -/
def twistedCharacter (χ : (Fin (n + 1) → Fˣ) → ℂ) (t : ℂ)
    (a : Fin (n + 1) → Fˣ) : ℂ :=
  χ a * (((borelModulus F a)⁻¹ : ℝ) : ℂ) *
    (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ t

/-- `χ δ⁻¹ |det|^t` is a finite function when `χ` is. -/
theorem isFiniteFunction_twistedCharacter {χ : (Fin (n + 1) → Fˣ) → ℂ}
    (hχ : IsFiniteFunction χ) (t : ℂ) : IsFiniteFunction (twistedCharacter F χ t) := by
  have hδ : IsFiniteFunction fun a : Fin (n + 1) → Fˣ =>
      (((borelModulus F a)⁻¹ : ℝ) : ℂ) :=
    IsFiniteFunction.of_mul_apply
      (Complex.continuous_ofReal.comp
        ((continuous_borelModulus F).inv₀ fun a => (borelModulus_pos F a).ne'))
      (fun b => (((borelModulus F b)⁻¹ : ℝ) : ℂ))
      (fun b a => by rw [borelModulus_mul, mul_inv, Complex.ofReal_mul])
  have hdet : IsFiniteFunction fun a : Fin (n + 1) → Fˣ =>
      (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ t :=
    IsFiniteFunction.of_mul_apply
      ((Complex.continuous_ofReal.comp (continuous_normalizedAbs_prod F)).cpow continuous_const
        fun a => Complex.ofReal_mem_slitPlane.2 (normalizedAbs_prod_pos F a))
      (fun b => (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (b i : F)) : ℝ) : ℂ) ^ t)
      (fun b a => by
        rw [normalizedAbs_prod_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (normalizedAbs_prod_pos F b).le
            (normalizedAbs_prod_pos F a).le])
  exact (hχ.mul hδ).mul hdet

/-- The slice integral of `Φ(· k)`, as a Schwartz–Bruhat function on `F^(n+1)`. -/
def sliceTest (ψ : UnitaryAdditiveCharacter F) (Φ : MatrixTestFunction n F)
    (k : Langlands.GeneralLinear (n + 1) F) :
    SchwartzBruhat (Fin (n + 1) → F) :=
  ⟨_, Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral_rightTranslate_mem ψ Φ k⟩

theorem sliceTest_apply (ψ : UnitaryAdditiveCharacter F)
    (Φ : MatrixTestFunction n F) (k : Langlands.GeneralLinear (n + 1) F)
    (x : Fin (n + 1) → F) :
    sliceTest F ψ Φ k x = Langlands.AllField.GodementJacquet.WhittakerSlice.sliceIntegral F ψ (fun M => Φ (M * k.val)) x :=
  rfl

/-- **Rationality of full-matrix Whittaker integrals.** Assume
`FiniteFunctionMellinStatement`, and let `W` satisfy `IsWhittakerLike`. If
`∫ Φ(g) W(g) |det g|^s dg` converges absolutely on a right half-plane, then for
every `t` the function `s ↦ ∫ Φ(g) W(g) |det g|^(s + t) dg` has a rational
continuation in `q^(-s)`. -/
theorem IsWhittakerLike.hasRationalContinuation (hFFM : FiniteFunctionMellinStatement.{uF})
    {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F) (t : ℂ)
    (hconv : ∃ c : ℝ, ∀ s : ℂ, c < s.re → Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s W) :
    ∃ R : RationalFunctions,
      HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
        (fun s => Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + t) W) R := by
  classical
  obtain ⟨K₀, S, -, hSK, hinv, -, hsum⟩ := hW.exists_cosetSum F Φ
  have hexp : ∀ k : Langlands.GeneralLinear (n + 1) F,
      ∃ X : Finset ((Fin (n + 1) → Fˣ) → ℂ), (∀ χ ∈ X, IsFiniteFunction χ) ∧
        ∃ φ : ((Fin (n + 1) → Fˣ) → ℂ) → SchwartzBruhat (Fin n → F),
          ∀ a, W (Iwasawa.diagonalUnits a * k) = ∑ χ ∈ X, φ χ (ratios F a) * χ a :=
    hW.expansion
  choose X hX φ hφ using hexp
  have hM : ∀ k, ∀ χ ∈ X k,
      (∃ c : ℝ, ∀ s : ℂ, c < s.re →
        Integrable (torusIntegrand F (φ k χ) (sliceTest F ψ Φ k) (twistedCharacter F χ t) s)
          (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F)) ∧
      ∃ R : RationalFunctions,
        HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
          (fun s => ∫ a, torusIntegrand F (φ k χ) (sliceTest F ψ Φ k)
              (twistedCharacter F χ t) s a
            ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) R :=
    fun k χ hχ => torusMellin F hFFM _ (isFiniteFunction_twistedCharacter F (hX k χ hχ) t)
      (φ k χ) (sliceTest F ψ Φ k)
  obtain ⟨c₀, hc₀⟩ := hconv
  obtain ⟨c₁, hc₁⟩ := exists_common_halfPlane S _ fun k _ =>
    exists_common_halfPlane (X k) _ fun χ hχ => (hM k χ hχ).1
  have key : ∀ s : ℂ, c₀ - t.re < s.re → c₁ < s.re →
      Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + t) W =
        ∑ k ∈ S, ((generalLinearHaar F n).real
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F)) : ℂ) *
          ∑ χ ∈ X k, ∫ a, torusIntegrand F (φ k χ) (sliceTest F ψ Φ k)
              (twistedCharacter F χ t) s a
            ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F := by
    intro s hs₀ hs₁
    have hI : Integrable (Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ (s + t) W)
        (generalLinearHaar F n) :=
      hc₀ (s + t) (by rw [Complex.add_re]; linarith)
    change ∫ g, Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ (s + t) W g
      ∂generalLinearHaar F n = _
    rw [integral_iwasawa F _ hI]
    refine (hsum _ ?_).trans ?_
    · intro k _ k₀ hk₀
      simp_rw [← mul_assoc _ k k₀, fun g => hinv (s + t) g k₀ hk₀]
    · refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      rw [← integral_finsetSum (X k) fun χ hχ => hc₁ s hs₁ k hk χ hχ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      have hne : (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) :
          ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (normalizedAbs_prod_pos F a).ne'
      simp only []
      rw [integral_unipotent_matrixIntegrand F hW.equivariant Φ (s + t) a (hSK hk), hφ k a,
        Complex.cpow_add _ _ hne]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      simp only [torusIntegrand, twistedCharacter, sliceTest_apply]
      ring
  have hrat : ∃ R : RationalFunctions,
      HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
        (fun s => ∑ k ∈ S, ((generalLinearHaar F n).real
            (K₀ : Set (Langlands.GeneralLinear (n + 1) F)) : ℂ) *
          ∑ χ ∈ X k, ∫ a, torusIntegrand F (φ k χ) (sliceTest F ψ Φ k)
              (twistedCharacter F χ t) s a
            ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) R := by
    refine exists_continuation_sum S _ fun k _ => ?_
    obtain ⟨R, hR⟩ := exists_continuation_sum (X k) _ fun χ hχ => (hM k χ hχ).2
    exact ⟨_, hasRationalContinuation_const_mul _ hR⟩
  obtain ⟨R, hR⟩ := hrat
  exact ⟨R, continuation_of_eq_on_right hR ⟨max (c₀ - t.re) c₁, fun s hs =>
    key s ((le_max_left _ _).trans_lt hs) ((le_max_right _ _).trans_lt hs)⟩⟩

end Padic

end Langlands.AllField.GodementJacquet.WhittakerTorus
