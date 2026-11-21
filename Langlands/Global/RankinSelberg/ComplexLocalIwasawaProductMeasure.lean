import Langlands.Global.RankinSelberg.ComplexLocalIwasawaMeasure

/-! # Iwasawa integration on the complex unipotent quotient -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.Archimedean.ComplexDuality Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped ENNReal NNReal Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa

open ArchimedeanLocal ComplexLocalWhittakerGauge

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

variable {r : ℕ}

local notation "n" => r + 1
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Y" => Fin n → ℝ
local notation "K" => unitaryCompact ℂ n
local notation "μK" => unitaryHaar n

/-- The full quotient integral in toral and compact coordinates, with respect to
Lebesgue measure and normalized unitary Haar. -/
def ComplexLocalIwasawaProductMeasureStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r),
    ∃ (c : ℝ≥0) (L : Y →L[ℝ] ℝ), ∀ F : Q → ℝ≥0∞, Measurable F →
      (∫⁻ q, F q ∂D.measure) =
        (c : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) *
          (∫⁻ k, F ((quotientHomeomorph n).symm (y, k)) ∂μK)

set_option maxHeartbeats 1000000 in
theorem complexLocalIwasawaProductMeasure :
    ComplexLocalIwasawaProductMeasureStatement (r := r) := by
  intro D
  let e := quotientHomeomorph n
  let : SigmaCompactSpace Q := e.isClosedEmbedding.sigmaCompactSpace
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : SigmaFinite D.measure := inferInstance
  obtain ⟨c, L, hT⟩ := complexIwasawaToralMeasure r D
  refine ⟨c, L, fun F hF => ?_⟩
  let B (y : Y) := ∫⁻ k, F (e.symm (y, k)) ∂μK
  let A (q : Q × K) := F (e.symm ((e q.1).1, (e q.1).2 * q.2))
  have hB : Measurable B :=
    (hF.comp e.symm.continuous.measurable).lintegral_prod_right'
  have hA : Measurable A :=
    hF.comp (e.symm.continuous.comp
      ((continuous_fst.comp (e.continuous.comp continuous_fst)).prodMk
        ((continuous_snd.comp (e.continuous.comp continuous_fst)).mul continuous_snd))).measurable
  have hAction (q : Q) (k : K) :
      e.symm ((e q).1, (e q).2 * k) = rightTranslate N k.val q := by
    conv_rhs => rw [← e.symm_apply_apply q]
    change Quotient.mk _ (logTorus (e q).1 * ((e q).2 * k).val) =
      rightTranslate N k.val (Quotient.mk _ (logTorus (e q).1 * ((e q).2 : K).val))
    rw [rightTranslate_mk, Subgroup.coe_mul, mul_assoc]
  have hq (q : Q) : (∫⁻ k, A (q, k) ∂μK) = B (alphaQ q) := by
    let f (k : K) := F (e.symm ((e q).1, k))
    have hf : Measurable f :=
      hF.comp (e.symm.continuous.comp (continuous_const.prodMk continuous_id)).measurable
    change (∫⁻ k, f ((e q).2 * k) ∂μK) = ∫⁻ k, f k ∂μK
    exact (measurePreserving_mul_left μK (e q).2).lintegral_comp hf
  have hk (k : K) : (∫⁻ q, A (q, k) ∂D.measure) = ∫⁻ q, F q ∂D.measure := by
    simp only [A, hAction]
    exact (D.compatible.right_invariant k.val).lintegral_comp hF
  calc
    (∫⁻ q, F q ∂D.measure) = ∫⁻ k, ∫⁻ q, A (q, k) ∂D.measure ∂μK := by
      simp only [hk, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ q, ∫⁻ k, A (q, k) ∂μK ∂D.measure :=
      (lintegral_lintegral_swap (f := fun q k => A (q, k)) hA.aemeasurable).symm
    _ = ∫⁻ q, B (alphaQ q) ∂D.measure := lintegral_congr hq
    _ = _ := hT B hB

end Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa
