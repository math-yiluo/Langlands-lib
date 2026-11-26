import Langlands.Global.RankinSelberg.RealMatrixNormalizedGrowth
import Langlands.Global.RankinSelberg.RealLocalEqualGrowthStep
import Langlands.Global.RankinSelberg.RealMatrixCoefficientIntegrability
import Langlands.Global.RankinSelberg.RealLocalCompactFourierWeight

/-! # The matrix normalized equation for real principal-series coefficients

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData charData_character_apply)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open RealJacquet (HasRealPairNormalizedGrowth)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- Expansion of real principal-series positions does not change a list of characters. -/
theorem expand_map_character (cs : List RealCharacterData) :
    RealPrincipalSeries.expand (cs.map RealBlock.character) = cs.map RealBlock.character := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change RealBlock.character c :: RealPrincipalSeries.expand (cs.map RealBlock.character) =
      RealBlock.character c :: cs.map RealBlock.character
    rw [ih]

/-- The determinant sign character `charData e 0` takes the same value at the inverse
transpose. -/
theorem realDetCharacter_charData_zero_inverseTranspose {n : ℕ} (e : Fin 2)
    (g : Langlands.GeneralLinear n ℝ) :
    RealPrincipalSeries.realDetCharacter (charData e 0) (inverseTranspose n ℝ g) =
      RealPrincipalSeries.realDetCharacter (charData e 0) g := by
  rw [RealPrincipalSeries.realDetCharacter_inverseTranspose]
  set z := RealPrincipalSeries.realDetCharacter (charData e 0) g with hz
  have hsq : z * z = 1 := by
    rw [hz, RealPrincipalSeries.realDetCharacter_apply]
    change Langlands.Archimedean.RealJacquetFrobenius.charFun e 0 g.val.det *
      Langlands.Archimedean.RealJacquetFrobenius.charFun e 0 g.val.det = 1
    unfold Langlands.Archimedean.RealJacquetFrobenius.charFun
    set x : ℝ := g.val.det
    have hx : x ≠ 0 := (determinant g).ne_zero
    have hu : (x / |x|) * (x / |x|) = 1 := by
      rw [div_mul_div_comm, ← sq, ← sq, sq_abs, div_self (pow_ne_zero 2 hx)]
    rw [Complex.cpow_zero, mul_one, ← mul_pow, ← Complex.ofReal_mul, hu, Complex.ofReal_one,
      one_pow]
  exact inv_eq_of_mul_eq_one_right hsq

/-- The weighted matrix integrand of `realWeightedMatrixIntegral` is the real matrix zeta
kernel of the coefficient twisted by the determinant sign character. -/
theorem realWeightedMatrixTest_mul_eq_zetaKernel {t : ℕ} (e : Fin 2)
    (Ψ : Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ → ℂ) (b : Langlands.GeneralLinear (t + 2) ℝ → ℂ)
    (w : ℂ) (g : Langlands.GeneralLinear (t + 2) ℝ) :
    realWeightedMatrixTest (charData e 0) Ψ (w + ((t : ℂ) + 1) / 2) g * b g =
      GodementJacquet.realMatrixZetaKernel (r := t + 1)
        (fun g => RealPrincipalSeries.realDetCharacter (charData e 0) g * b g) Ψ w g := by
  have hpos : (0 : ℝ) < |g.val.det| := abs_pos.mpr (determinant g).ne_zero
  have hpow : ArchimedeanLocal.detPower (K := ℝ) ArchimedeanLocal.realNormalizedAbs g
      (w + ((t : ℂ) + 1) / 2) = ((|g.val.det| : ℝ) : ℂ) ^ (w + ((t : ℂ) + 1) / 2) := by
    unfold ArchimedeanLocal.detPower ArchimedeanLocal.realNormalizedAbs
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, mul_comm]
  have hcast : (((t + 1 : ℕ) : ℂ)) = (t : ℂ) + 1 := by push_cast; ring
  unfold GodementJacquet.realMatrixZetaKernel
  rw [hcast, hpow]
  change Ψ g.val * ((((charData e 0).character (determinant g)) : ℂ) *
      ((|g.val.det| : ℝ) : ℂ) ^ (w + ((t : ℂ) + 1) / 2)) * b g =
    Ψ g.val * ((((charData e 0).character (determinant g)) : ℂ) * b g) *
      ((|g.val.det| : ℝ) : ℂ) ^ (w + ((t : ℂ) + 1) / 2)
  ring

/-- The normalized property depends on the second list only through its value. -/
theorem hasRealPairNormalizedGrowth_list_congr {ds es es' dds : List RealBlock} {b : ℝˣ}
    {c : ℝ≥0} {hc : 0 < c} {sign : ℂ} {I Id : ℂ → ℂ} (h : es = es')
    (hI : HasRealPairNormalizedGrowth ds es dds (es.map RealLocalJacquet.dualBlock) b c hc sign
      I Id) :
    HasRealPairNormalizedGrowth ds es' dds (es'.map RealLocalJacquet.dualBlock) b c hc sign
      I Id := by
  subst h
  exact hI

/-- The normalized property depends on the positive scale only through its value. -/
theorem hasRealPairNormalizedGrowth_scale_congr {ds es dds ees : List RealBlock} {b : ℝˣ}
    {c c' : ℝ≥0} {hc : 0 < c} {hc' : 0 < c'} {sign : ℂ} {I Id : ℂ → ℂ} (h : c = c')
    (hI : HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id) :
    HasRealPairNormalizedGrowth ds es dds ees b c' hc' sign I Id := by
  subst h
  exact hI

variable (t : ℕ) in
/-- The matrix normalized equation holds at every rank, for every standard vector and every
square Schwartz test. The hypothesis on the left orthogonal span of the test is not used. -/
theorem realMatrixCoefficientGrowth : RealMatrixCoefficientGrowthPremise t := by
  intro D' a e fs hfs f Ψ _ ℓ hℓ
  let es : List RealBlock := fs.map RealBlock.character
  have : D'.groupHaar.IsHaarMeasure := D'.groupHaar_isHaar
  let κ : Measure (unitaryCompact ℝ (t + 2)) := Measure.haar
  have hes : realRank es = t + 2 := by
    rw [realRank_map_character, hfs]
  refine ⟨exists_realWeightedMatrix_integrable D'.groupHaar e es ℓ hℓ f Ψ
    (realRectangularSchwartzFourier (-a) Ψ), ?_⟩
  have key := GodementJacquet.realMatrixPairNormalizedGrowth (r := t + 1) D'.groupHaar κ es hes
    (RealPrincipalSeries.expandedSmoothInclusion (t + 1) es f) ℓ hℓ (charData e 0) Ψ (-a)
  dsimp only at key
  have hexp : RealPrincipalSeries.expand es = es := expand_map_character fs
  have hscale : NNReal.sqrt ‖((-a : ℝˣ) : ℝ)‖₊ = NNReal.sqrt ‖(a : ℝ)‖₊ := by
    rw [Units.val_neg, nnnorm_neg]
  refine (hasRealPairNormalizedGrowth_scale_congr hscale
    (hasRealPairNormalizedGrowth_list_congr hexp key)).congr (τ := 0) ?_ ?_
  · intro w _
    unfold GodementJacquet.realMatrixZeta realWeightedMatrixIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (realWeightedMatrixTest_mul_eq_zetaKernel e Ψ (realStandardMatrixCoefficient es ℓ f)
      w g).symm
  · intro w _
    unfold GodementJacquet.realMatrixZeta realWeightedMatrixIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    dsimp only
    rw [realWeightedMatrixTest_mul_eq_zetaKernel e _
      (realStandardMatrixCoefficient es ℓ f ∘ inverseTranspose (t + 2) ℝ) w g]
    unfold GodementJacquet.realMatrixZetaKernel
    rw [← matrixTransform_eq_realRectangularSchwartzFourier]
    simp only [Function.comp_apply]
    rw [realDetCharacter_charData_zero_inverseTranspose]
    rfl

/-- The matrix normalized equation `RealMatrixCoefficientGrowthPremise t` at every rank `t`. -/
def RealMatrixCoefficientGrowthStatement : Prop :=
  ∀ t : ℕ, RealMatrixCoefficientGrowthPremise t

theorem realMatrixCoefficientGrowthStatement : RealMatrixCoefficientGrowthStatement :=
  realMatrixCoefficientGrowth

/-- The positive equal-rank continuation target follows from the principal-series inclusion,
the canonical range and canonical evaluation premises and adjacent character growth at every
rank. The matrix premise of `RealLocalUniformPositiveEqualContinuationPremisesStatement` is
removed. -/
def RealLocalUniformPositiveEqualContinuationReducedPremisesStatement : Prop :=
  RealUniformPrincipalSeriesInclusionStatement → RealUniformCanonicalRangePremise →
    RealCanonicalStandardEvaluationPremise →
    (∀ t : ℕ, RealJacquet.RealLocalAdjacentCharacterGrowthAtRank t) →
    RealLocalUniformPositiveEqualContinuationStatement

theorem realLocalUniformPositiveEqualContinuation_of_reducedPremises :
    RealLocalUniformPositiveEqualContinuationReducedPremisesStatement :=
  fun hI hRange hEval hAdj =>
    realLocalUniformPositiveEqualContinuation_of_premises hI hRange hEval
      realMatrixCoefficientGrowth hAdj

end Langlands.Global.RankinSelbergGlobal.RealGodement
