import Langlands.Global.RankinSelberg.RealLowerBlockQuotientHaar
import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear
import Langlands.Representation.RankinSelberg.InducedTailIntermediateComparison

/-! # The real rank-raising determinant and integral identity -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral

open Langlands.GeneralLinear Langlands.QuotientIntegration Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure unipotent_det)
open Langlands.RankinSelberg.InducedTailIntermediate (det_lowerBlockPair)
open ArchimedeanLocal RealLowerBlockMeasure RealLowerBlockQuotientHaar RealLastPivotChart
open ArchimedeanRealPairIdentity (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs
  sigmaFinite_measure sigmaFinite_rect)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (lowerTriangularSubgroup n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (lowerTriangularSubgroup n ℝ) := ⟨rfl⟩

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => fun r => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Q" => fun r => LeftUnipotentQuotient r ℝ
local notation "B" => lowerTriangularSubgroup 1 ℝ
local notation "X" => fun r => Matrix (Fin 1) (Fin (r + 1)) ℝ
local notation "chart" => fun r => lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)

/-- The determinant power on the real left-unipotent quotient. -/
def realQuotientDetPower {r : ℕ} (q : Q r) (s : ℂ) : ℂ :=
  ArchimedeanLocal.detPower realNormalizedAbs q.out s

private theorem continuous_realQuotientDetPower {r : ℕ} (s : ℂ) :
    Continuous (fun q : Q r => realQuotientDetPower q s) := by
  change Continuous (fun q : Q r => Complex.exp (s * (Real.log (quotientDetAbs q) : ℂ)))
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_quotientDetAbs.log fun q => (quotientDetAbs_pos q).ne')))

private def trailAbs (h : B) : ℝ := |h.val.val.det|

private theorem trailAbs_pos (h : B) : 0 < trailAbs h :=
  abs_pos.mpr (determinant h.val).ne_zero

/-- The smaller diagonal matrix `diag(det h, 1, …, 1)` used to compensate the
trailing coordinate. -/
def rankRaisingDiagonal (r : ℕ) (h : B) : G r :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => if i = 0 then determinant h.val else 1)

private theorem det_rankRaisingDiagonal (r : ℕ) (h : B) :
    (rankRaisingDiagonal r h).val.det = h.val.val.det := by
  rw [rankRaisingDiagonal, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.det_diagonal,
    Finset.prod_eq_single (0 : Fin (r + 1))]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

private theorem continuous_rankRaisingDiagonal (r : ℕ) : Continuous (rankRaisingDiagonal r) := by
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, rankRaisingDiagonal, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [hi, ite_true, Matrix.GeneralLinearGroup.val_det_apply]
    exact (Units.continuous_val.comp
      (continuous_subtype_val : Continuous (Subtype.val : B → Langlands.GeneralLinear 1 ℝ))).matrix_det
  · simp only [hi, ite_false, Units.val_one]
    exact continuous_const

/-- The lower block `[a(h)⁻¹,0;x,h]` used to average right translates of
coefficients, where `a(h) = diag(det h, 1, …, 1)`. -/
def rankRaisingSmoothingMatrix {r : ℕ} (y : X r × B) : G (r + 1) :=
  lowerBlockPair (rankRaisingDiagonal r y.2)⁻¹ y.1 y.2

/-- The rank-raising argument in the larger quotient is the padded smaller
argument followed by the rank-raising right translate. -/
def rankRaisingArgument {r : ℕ} (q : Q r) (y : X r × B) : Q (r + 1) :=
  rightTranslate (N (r + 1)) (rankRaisingSmoothingMatrix y) (chart r (q, 0, 1))

/-- The same argument in actual lower-block quotient coordinates. -/
theorem rankRaisingArgument_eq {r : ℕ} (q : Q r) (y : X r × B) :
    rankRaisingArgument q y = chart r (rightTranslate (N r) (rankRaisingDiagonal r y.2)⁻¹ q, y) := by
  rcases y with ⟨x, h⟩
  induction q using Quotient.inductionOn with
  | _ g =>
    let a := (rankRaisingDiagonal r h)⁻¹
    change rightTranslate (N (r + 1)) (lowerBlockPair a x h)
      (lowerBlockQuotientChart (Quotient.mk _ g, 0, (1 : B))) =
        lowerBlockQuotientChart (rightTranslate (N r) a (Quotient.mk _ g), x, h)
    rw [lowerBlockQuotientChart_mk, rightTranslate_mk, rightTranslate_mk,
      lowerBlockQuotientChart_mk, lowerBlockPair_mul_lowerBlockPair]
    simp only [Matrix.zero_mul, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, zero_add, one_mul]

private theorem quotientDetAbs_mk {r : ℕ} (g : G r) :
    quotientDetAbs (Quotient.mk _ g : Q r) = |g.val.det| := by
  let f : G r → ℝ := fun x => |x.val.det|
  have hf (u : N r) (x : G r) : f (u.val * x) = f x := by
    simp only [f, Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
  exact RealEqualConvergence.out_eq_descend f hf (Quotient.mk _ g)

private theorem quotientDetAbs_chart {r : ℕ} (q : Q r) (y : X r × B) :
    quotientDetAbs (chart r (q, y)) = quotientDetAbs q * trailAbs y.2 := by
  rcases y with ⟨x, h⟩
  induction q using Quotient.inductionOn with
  | _ g =>
    change quotientDetAbs (lowerBlockQuotientChart (Quotient.mk _ g, x, h)) =
      quotientDetAbs (Quotient.mk _ g) * trailAbs h
    rw [lowerBlockQuotientChart_mk, quotientDetAbs_mk, quotientDetAbs_mk, det_lowerBlockPair, abs_mul, trailAbs]

private theorem quotientDetAbs_compensated {r : ℕ} (q : Q r) (h : B) :
    quotientDetAbs (rightTranslate (N r) (rankRaisingDiagonal r h)⁻¹ q) =
      quotientDetAbs q * (trailAbs h)⁻¹ := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk, quotientDetAbs_mk, quotientDetAbs_mk, Units.val_mul, Matrix.det_mul, abs_mul]
    congr 1
    change |((Matrix.GeneralLinearGroup.det ((rankRaisingDiagonal r h)⁻¹) : ℝˣ) : ℝ)| = _
    rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply,
      det_rankRaisingDiagonal, abs_inv, trailAbs]

/-- The rank-raising right translate leaves the determinant absolute value
of the padded argument equal to that of the smaller argument. -/
theorem quotientDetAbs_rankRaisingArgument {r : ℕ} (q : Q r) (y : X r × B) :
    quotientDetAbs (rankRaisingArgument q y) = quotientDetAbs q := by
  rw [rankRaisingArgument_eq, quotientDetAbs_chart, quotientDetAbs_compensated, mul_assoc,
    inv_mul_cancel₀ (trailAbs_pos y.2).ne', mul_one]

private def quotientWeight {r : ℕ} (q : Q r) : ℝ≥0 := (quotientDetAbs q).toNNReal⁻¹

private theorem continuous_quotientWeight {r : ℕ} : Continuous (quotientWeight (r := r)) :=
  (continuous_real_toNNReal.comp continuous_quotientDetAbs).inv₀ fun q =>
    (Real.toNNReal_pos.mpr (quotientDetAbs_pos q)).ne'

private theorem coe_quotientWeight {r : ℕ} (q : Q r) : (quotientWeight q : ℝ) = (quotientDetAbs q)⁻¹ := by
  rw [quotientWeight, NNReal.coe_inv, Real.coe_toNNReal _ (quotientDetAbs_pos q).le]

private theorem power_density_shift {r : ℕ} (q : Q r) (s : ℂ) :
    ((quotientDetAbs q)⁻¹ : ℝ) • realQuotientDetPower q s = realQuotientDetPower q (s - 1) := by
  have hlog : Complex.exp ((Real.log (quotientDetAbs q) : ℝ) : ℂ) = (quotientDetAbs q : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (quotientDetAbs_pos q)]
  change _ = Complex.exp ((s - 1) * (Real.log (quotientDetAbs q) : ℂ))
  rw [sub_mul, Complex.exp_sub, one_mul, hlog, div_eq_mul_inv,
    Complex.real_smul, Complex.ofReal_inv]
  exact mul_comm _ _

private def compensate {r : ℕ} (z : Q r × (X r × B)) : Q r × (X r × B) :=
  (rightTranslate (N r) (rankRaisingDiagonal r z.2.2)⁻¹ z.1, z.2)

private theorem measurePreserving_compensate {r : ℕ} (D : RealQuotientMeasureData r)
    (η : Measure (X r × B)) [SFinite η] :
    MeasurePreserving (compensate (r := r)) (D.measure.prod η) (D.measure.prod η) := by
  let := sigmaFinite_measure D
  let := D.unipotentHaar_rightInvariant
  have hdiag : Continuous (fun y : X r × B => (rankRaisingDiagonal r y.2)⁻¹) :=
    (continuous_rankRaisingDiagonal r).inv.comp continuous_snd
  let L (p : (X r × B) × Q r) : Q r × G r := (p.2, (rankRaisingDiagonal r p.1.2)⁻¹)
  have hL : Continuous L :=
    continuous_snd.prodMk (hdiag.comp continuous_fst)
  let R (z : Q r × G r) : Q r := rightTranslate (N r) z.2 z.1
  have hR : Continuous R :=
    continuous_rightTranslate_joint (N r)
  have hc : Continuous (R ∘ L) := hR.comp hL
  have hs := (MeasurePreserving.id η).skew_product
    (g := fun y q => rightTranslate (N r) (rankRaisingDiagonal r y.2)⁻¹ q) hc.measurable
    (Filter.Eventually.of_forall fun y => (D.compatible.right_invariant (rankRaisingDiagonal r y.2)⁻¹).map_eq)
  exact measurePreserving_swap.comp (hs.comp measurePreserving_swap)

/-- The averaged coefficient on the smaller quotient with the spectral power
one lower and with the factor `|det h|` in the averaging measure. -/
def averagedRankRaisingKernel {r : ℕ} (η : Measure (X r × B)) (F : Q (r + 1) → ℂ)
    (s : ℂ) (q : Q r) : ℂ :=
  realQuotientDetPower q (s - 1) *
    ∫ y, ((|y.2.val.val.det| : ℝ) : ℂ) * F (rankRaisingArgument q y) ∂η

/-- After averaging by the compensating right translates, the smaller quotient
integral is the larger one up to the positive measure comparison scalar. -/
def RealRankRaisingIntegralStatement : Prop :=
  ∀ (r : ℕ) (D : RealQuotientMeasureData r) (E : RealQuotientMeasureData (r + 1))
    (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B)
    [SigmaFinite ρ] [IsFiniteMeasureOnCompacts ρ] [ρ.IsMulRightInvariant], ρ ≠ 0 →
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Q (r + 1) → ℂ), Measurable F → ∀ s : ℂ,
      Integrable (fun q => F q * realQuotientDetPower q s) E.measure →
      Integrable (averagedRankRaisingKernel ((rectangularMeasure ν 1 (r + 1)).prod ρ) F s) D.measure ∧
      (∫ q, F q * realQuotientDetPower q s ∂E.measure) =
        (C : ℂ) * ∫ q, averagedRankRaisingKernel ((rectangularMeasure ν 1 (r + 1)).prod ρ) F s q ∂D.measure

theorem realRankRaisingIntegral : RealRankRaisingIntegralStatement := by
  intro r D E ν ρ _ _ _ hρ
  obtain ⟨C, hC, hE⟩ := realLowerBlockQuotientHaar r D E ν ρ hρ
  refine ⟨C, hC, fun F hF s hi => ?_⟩
  let η := (rectangularMeasure ν 1 (r + 1)).prod ρ
  let μ := D.measure.prod η
  let := sigmaFinite_measure D
  let := sigmaFinite_rect ν 1 (r + 1)
  let w : Q r × (X r × B) → ℝ≥0 := quotientWeight ∘ Prod.fst
  have hw : Measurable w := (continuous_quotientWeight.comp continuous_fst).measurable
  have hP : lowerBlockProduct D ν ρ = μ.withDensity (fun z => (w z : ℝ≥0∞)) := by
    have hWeight : lowerBlockDensity (r := r) 1 = fun q => (quotientWeight q : ℝ≥0∞) := by
      funext q
      simp only [lowerBlockDensity, pow_one, quotientWeight]
    unfold lowerBlockProduct
    rw [hWeight]
    exact prod_withDensity_left (ν := η) continuous_quotientWeight.measurable.coe_nnreal_ennreal
  let I := fun q : Q (r + 1) => F q * realQuotientDetPower q s
  let M := fun z : Q r × (X r × B) => w z • I (chart r z)
  have hI : Measurable I := hF.mul (continuous_realQuotientDetPower s).measurable
  have hchart : Measurable (chart r) := isOpenEmbedding_realLastPivotChart.continuous.measurable
  have hmap : Integrable I ((lowerBlockProduct D ν ρ).map (chart r)) := by
    rw [hE] at hi
    exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top).mp hi
  have hcomp : Integrable (I ∘ chart r) (lowerBlockProduct D ν ρ) :=
    (integrable_map_measure hI.aestronglyMeasurable hchart.aemeasurable).mp hmap
  have hM : Integrable M μ := by
    rw [hP] at hcomp
    exact (integrable_withDensity_iff_integrable_smul hw).mp hcomp
  let K := fun z : Q r × (X r × B) => realQuotientDetPower z.1 (s - 1) *
    ((trailAbs z.2.2 : ℂ) * F (rankRaisingArgument z.1 z.2))
  have hKM : K = M ∘ compensate := by
    funext z
    have he : chart r (compensate z) = rankRaisingArgument z.1 z.2 := (rankRaisingArgument_eq _ _).symm
    have hwc : (w (compensate z) : ℝ) = (quotientDetAbs z.1)⁻¹ * trailAbs z.2.2 := by
      change (quotientWeight (rightTranslate (N r) (rankRaisingDiagonal r z.2.2)⁻¹ z.1) : ℝ) = _
      rw [coe_quotientWeight, quotientDetAbs_compensated, mul_inv, inv_inv]
    have hPow : realQuotientDetPower (rankRaisingArgument z.1 z.2) s = realQuotientDetPower z.1 s := by
      change Complex.exp (s * (Real.log (quotientDetAbs (rankRaisingArgument z.1 z.2)) : ℂ)) = _
      rw [quotientDetAbs_rankRaisingArgument]
      rfl
    change K z = ((w (compensate z) : ℝ) : ℂ) *
      (F (chart r (compensate z)) * realQuotientDetPower (chart r (compensate z)) s)
    rw [he, hwc, hPow, Complex.ofReal_mul]
    have hs := power_density_shift z.1 s
    rw [Complex.real_smul] at hs
    calc
      K z = ((quotientDetAbs z.1)⁻¹ : ℝ) *
          realQuotientDetPower z.1 s * ((trailAbs z.2.2 : ℂ) * F (rankRaisingArgument z.1 z.2)) := by
            rw [hs]
      _ = _ := by ring
  have hp := measurePreserving_compensate D η
  have hK : Integrable K μ := by
    rw [hKM]
    exact hp.integrable_comp_of_integrable hM
  have hAvg : averagedRankRaisingKernel η F s = fun q => ∫ y, K (q, y) ∂η := by
    funext q
    exact (integral_const_mul _ _).symm
  refine ⟨by rw [hAvg]; exact hK.integral_prod_left, ?_⟩
  change (∫ q, I q ∂E.measure) = (C : ℂ) * ∫ q, averagedRankRaisingKernel η F s q ∂D.measure
  have hPresIntegr : (∫ z, M (compensate z) ∂μ) = ∫ z, M z ∂μ := by
    have hMeas : AEStronglyMeasurable M (μ.map compensate) := hp.map_eq.symm ▸ hM.aestronglyMeasurable
    rw [← integral_map hp.measurable.aemeasurable hMeas, hp.map_eq]
  rw [hE, integral_smul_measure, integral_map hchart.aemeasurable hI.aestronglyMeasurable,
    hP, integral_withDensity_eq_integral_smul hw, hAvg, ← integral_prod K hK, hKM]
  rw [show (∫ z, (M ∘ compensate) z ∂μ) = (∫ z, M z ∂μ) from hPresIntegr,
    ENNReal.toReal_ofReal hC.le, Complex.real_smul]

end Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral
