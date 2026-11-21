import Langlands.Global.RankinSelberg.ComplexGapNormalizedPowerMoment
import Langlands.Global.RankinSelberg.ComplexGapOrdinarySeparation
import Langlands.Global.RankinSelberg.ComplexGodementBlockUnfolding

/-! # The ordinary zeta integral on the separated determinant chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinarySeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant rankInclusion weylLong)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap rightTranslate rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexSelfDualMeasure
  complexUnequalIntegrand complexUnequalIntegral)
open ArchimedeanRealPairIdentity (ofReal_cpow_eq_exp)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapAlternateWeighted (leadingSide)
open ComplexGapDualChart (retainedTail)
open ComplexGapExactRestriction (rotatedValue)
open ComplexGapNormalizedRestriction (unitOrdinaryKernel)
open ComplexGapNormalizedWeighted (complexGapNormalizedPowerMoment padGL_eq_rankInclusion quotientDetAbs_mk)
open ComplexGapRankCoordinates (rankLT)
open ComplexGapSeparatedKernels (detPower_add retainedCoefficient unitOrdinaryKernel_separate)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest)
open ComplexGapSplitFourier (columnTransform)
open ComplexGapTriangularChart (Outer outerMeasure)
open ComplexGapUnitDeterminant (unitOuterMeasure)
open ComplexGapWeylRestriction (reverseTail)
open ComplexGodementBlockUnfolding (quotientShift measurePreserving_quotientShift)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexUnequalFamily (HasLeftCharacter ordinaryKernel_mk)
open ComplexUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs
  complexUnequalIntegrand_eq_mul sigmaFinite_quotient)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "ρ" => ArchimedeanLocal.translateFunction

variable (t q : ℕ)
local notation "k" => t + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "Side" => Outer k q × U (q + 1)
local notation "Coords" => Q t × Side
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ
local notation "h" => rankLT t q
local notation "h'" => rankLT t (q + 1)
local notation "lead" => fun p : Side => Prod.fst (Prod.fst (Prod.fst (Prod.fst p)))
local notation "MellinShift" => (((q + 1 : ℕ) : ℂ) / 2)

/-- The actual ordinary Weyl constant on the rotated value. -/
def ordinaryWeylPhase (d : ComplexCharacterData) : ℂ :=
  (d.character (determinant (weylLong (q + 2) ℂ)) : ℂ) * (d.character ((-1 : ℂˣ) ^ n) : ℂ)

/-- The two determinant variables of the ordinary separated chart multiply to the zeta determinant. -/
def ordinaryProductDet (p : Coords) : ℝ := quotientDetAbs p.1 * δ (lead p.2)

theorem ordinaryProductDet_pos (p : Coords) : 0 < ordinaryProductDet t q p :=
  mul_pos (quotientDetAbs_pos p.1) (Langlands.GodementJacquet.complexNormalizedAbs_det_pos _)

theorem measurable_ordinaryProductDet : Measurable (ordinaryProductDet t q) := by
  have hLead : Continuous (fun p : Coords => lead p.2) := by fun_prop
  exact (continuous_quotientDetAbs.comp continuous_fst).measurable.mul
    ((Units.continuous_val.comp hLead).matrix_det.norm.pow 2).measurable

/-- The independent profiles multiply the separated kernel at unit profiles. -/
theorem ordinarySeparatedKernel_mul_profiles (dual : Bool) (a : ℂˣ) (d : ComplexCharacterData)
    (T : GodementColumnFactors k q) (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Coords) :
    ordinarySeparatedKernel t q dual a d T W V f₁ f₂ p =
      ordinarySeparatedKernel t q dual a d T W V (fun _ => 1) (fun _ => 1) p *
        (f₁ (quotientDetAbs p.1) * f₂ (δ (leadingSide dual (lead p.2)))) := by
  simp only [ordinarySeparatedKernel, weightedOrdinary, mul_one]
  ring

set_option maxHeartbeats 850000 in
/-- The unweighted chart kernel is a.e. strongly measurable and has all sufficiently large absolute moments. -/
theorem ordinaryMellinData (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU n))
    (hκ : κ.IsHaarMeasure) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (ds es : List ComplexCharacterData) (W : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel t es a) :
    let μ := D.measure.prod (ordinaryChartMeasure t q a κ)
    let F := ordinarySeparatedKernel t q false a d T W.val V.val (fun _ => 1) (fun _ => 1)
    AEStronglyMeasurable F μ ∧ ∃ σ : ℝ, ∀ x : ℝ, σ ≤ x →
      Integrable (fun p => ‖F p‖ * ordinaryProductDet t q p ^ x) μ := by
  intro μ F
  let β := (d.exponent + (t : ℂ) / 2).re
  obtain ⟨b, hMoment⟩ := complexGapNormalizedPowerMoment t q a D κ hκ ds es W V β
  let σ := max 0 b
  have hW (p : Outer k q) : ‖chartMultiplier t q false d p‖ ≤ δ p.1.1.1 ^ β := by
    rw [norm_chartMultiplier]
    rfl
  have hMoment' (z : ℝ) (hz : σ ≤ z) :
      Integrable (fun p => F p * ((ordinaryProductDet t q p ^ z : ℝ) : ℂ)) μ := by
    let f (x : ℝ) : ℂ := (x ^ z : ℝ)
    have hC : Integrable (comparisonChartKernel t q false a d T W.val V.val f f)
        (ComplexGapNormalizedWeighted.normalizedGapMeasure t q a D (comparisonRectangleMeasure t q false a) κ) :=
      hMoment z ((le_max_right _ _).trans hz) (rectangularLeading t q false a T) (T.tail (Fin.last (q + 1)))
        (columnTransform a (T.tail 0)) ((reverseTail k q T).partial k q a).later
        (chartMultiplier t q false d) (measurable_chartMultiplier t q false d) hW
    have hI := (complexGapOrdinarySeparation t q D a κ hκ false d T ds W V.val f f hC).1
    refine hI.congr (ae_of_all _ fun p => ?_)
    rw [ordinarySeparatedKernel_mul_profiles]
    change F p * (((quotientDetAbs p.1 ^ z : ℝ) : ℂ) * ((δ (lead p.2) ^ z : ℝ) : ℂ)) =
      F p * (((quotientDetAbs p.1 * δ (lead p.2)) ^ z : ℝ) : ℂ)
    rw [← Complex.ofReal_mul,
      Real.mul_rpow (quotientDetAbs_pos p.1).le (Langlands.GodementJacquet.complexNormalizedAbs_det_pos _).le]
  have hσ : 0 ≤ σ := le_max_left _ _
  have hm : Measurable (fun p => (((ordinaryProductDet t q p ^ σ : ℝ) : ℂ))⁻¹) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_rpow_const hσ)).measurable.comp
      (measurable_ordinaryProductDet t q)).inv
  refine ⟨((hMoment' σ le_rfl).aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
    (ae_of_all _ fun p => ?_), σ, fun z hz => ?_⟩
  · have hp : ((ordinaryProductDet t q p ^ σ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (ordinaryProductDet_pos t q p) σ).ne'
    change F p * ((ordinaryProductDet t q p ^ σ : ℝ) : ℂ) * ((ordinaryProductDet t q p ^ σ : ℝ) : ℂ)⁻¹ = F p
    rw [mul_assoc, mul_inv_cancel₀ hp, mul_one]
  · refine (hMoment' z hz).norm.congr (ae_of_all _ fun p => ?_)
    change ‖F p * ((ordinaryProductDet t q p ^ z : ℝ) : ℂ)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (ordinaryProductDet_pos t q p).le z)]

private theorem translated_left {m : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel m ds a) (z : G (m + 1)) : HasLeftCharacter a (ρ z W.val) := by
  intro u g
  change W.val ((u.val * g) * z) = _
  rw [mul_assoc, complexWhittakerModel_left_equivariant W.2 _ u.2]
  rfl

private def ordinaryBeforeKernel (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (s : ℂ) (p : Coords) : ℂ :=
  unitOrdinaryKernel k q a d T W p.1.out 0 p.2.1 p.2.2 * V p.1.out *
    P p.1.out (0 - MellinShift) * (quotientDetAbs p.1 : ℂ) ^ s

set_option maxHeartbeats 1400000 in
private theorem ordinaryKernel_shift (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    {ds es : List ComplexCharacterData} (W : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel t es a)
    (s : ℂ) (x : Q t) (p : Side) :
    let v := (rightTranslate (U k) (lead p)⁻¹ x, p)
    ordinarySeparatedKernel t q false a d T W.val V.val (fun _ => 1) (fun _ => 1) v *
      (ordinaryProductDet t q v : ℂ) ^ s = ordinaryBeforeKernel t q a d T W.val V.val s (x, p) := by
  intro v
  let z := lead p
  let g := x.out
  let y := g * z⁻¹
  let C := retainedTail k q p.1 p.2
  have hv : v = (Quotient.mk _ y, p) := by
    apply Prod.ext
    · change rightTranslate (U k) z⁻¹ x = Quotient.mk _ (x.out * z⁻¹)
      conv_lhs => rw [← Quotient.out_eq x]
      exact rightTranslate_mk _ _ _
    · rfl
  have hmul (A B : H) : δ (A * B) = δ A * δ B := by
    simp only [Units.val_mul, Matrix.det_mul, complexNormalizedAbs, norm_mul, mul_pow]
  have hdet : ordinaryProductDet t q v = quotientDetAbs x := by
    rw [hv]
    change quotientDetAbs (Quotient.mk _ y : Q t) * δ z = δ g
    rw [quotientDetAbs_mk, ← hmul, show y * z = g from inv_mul_cancel_right g z]
  have hV : HasLeftCharacter (-(-a)) (ρ z V.val) := by simpa only [neg_neg] using translated_left V z
  have hpad : padGL (Nat.succ_le_succ (Nat.le_of_lt h)) y = rankInclusion (q + 1) y := padGL_eq_rankInclusion k q y
  have hgap : r - t = q + 1 := by omega
  rw [hdet, hv]
  simp only [ordinarySeparatedKernel, weightedOrdinary, leadingSide, Bool.false_eq_true, ite_false, mul_one]
  rw [ordinaryKernel_mk h (translated_left W C⁻¹) hV, hpad, hgap]
  have hs := unitOrdinaryKernel_separate t q a d T W.val y p.1 p.2 0 0
  change P (y * z) (0 - MellinShift) * unitOrdinaryKernel k q a d T W.val (y * z) 0 p.1 p.2 =
    retainedCoefficient t q a d T C * (W.val (rankInclusion (q + 1) y * C⁻¹) * P y (0 - MellinShift)) *
      squareKernel d (leadingSquareTest t q C T.leading) (fun _ => 1) (0 + 0) z at hs
  have hy : y * z = g := inv_mul_cancel_right g z
  rw [hy, zero_add] at hs
  change retainedCoefficient t q a d T C *
      (W.val (rankInclusion (q + 1) y * C⁻¹) * V.val (y * z) * P y (0 - MellinShift)) *
      squareKernel d (leadingSquareTest t q C T.leading) (fun _ => 1) 0 z * (quotientDetAbs x : ℂ) ^ s = _
  rw [hy]
  calc
    _ = (retainedCoefficient t q a d T C * (W.val (rankInclusion (q + 1) y * C⁻¹) * P y (0 - MellinShift)) *
      squareKernel d (leadingSquareTest t q C T.leading) (fun _ => 1) 0 z) * V.val g * (quotientDetAbs x : ℂ) ^ s := by ring
    _ = _ := by rw [← hs]; unfold ordinaryBeforeKernel; dsimp only [g]; ring

/-- The fixed ordinary restriction with one chart constant gives the exact Mellin identity on a right half-plane. -/
def ComplexGapOrdinaryMellinStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU n)), κ.IsHaarMeasure →
    ∀ (c : ℝ≥0) (d : ComplexCharacterData) (T : GodementColumnFactors k q) (Φ : 𝓢(Rect, ℂ))
      (ds es : List ComplexCharacterData) (W : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel t es a),
    let U₀ := rotatedValue t q a d Φ W.val 0
    (∀ g : H, U₀ (padGL (Nat.succ_le_succ (Nat.le_of_lt h')) g) = ordinaryWeylPhase t q d * P g (1 / 2) * (c : ℂ) *
      ∫ p, (∫ Z, unitOrdinaryKernel k q a d T W.val g 0 p Z ∂entryHaar (complexSelfDualMeasure a) (q + 1))
        ∂unitOuterMeasure k q (complexSelfDualMeasure a) κ) →
    let μ := D.measure.prod (ordinaryChartMeasure t q a κ)
    let F := ordinarySeparatedKernel t q false a d T W.val V.val (fun _ => 1) (fun _ => 1)
    AEStronglyMeasurable F μ ∧ ∃ σ : ℝ, ∀ s : ℂ, σ ≤ s.re →
      Integrable (fun p => ‖F p‖ * ordinaryProductDet t q p ^ s.re) μ ∧
      complexUnequalIntegral h' D U₀ V.val s = (ordinaryWeylPhase t q d * (c : ℂ)) *
        ∫ p, F p * (ordinaryProductDet t q p : ℂ) ^ s ∂μ

set_option maxHeartbeats 1400000 in
theorem complexGapOrdinaryMellin : ComplexGapOrdinaryMellinStatement t q := by
  intro D a κ hκ c d T Φ ds es W V U₀ hExact μ F
  obtain ⟨hF, σ, hI⟩ := ordinaryMellinData t q D a κ hκ d T ds es W V
  refine ⟨hF, σ, fun s hs => ⟨hI s.re hs, ?_⟩⟩
  let η := ordinaryChartMeasure t q a κ
  let C := ordinaryWeylPhase t q d * (c : ℂ)
  let B := ordinaryBeforeKernel t q a d T W.val V.val s
  let J := fun p : Coords => F p * (ordinaryProductDet t q p : ℂ) ^ s
  have hPow : Measurable (fun p : Coords => (ordinaryProductDet t q p : ℂ) ^ s) := by
    simp_rw [ofReal_cpow_eq_exp (ordinaryProductDet_pos t q _)]
    exact Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp (measurable_ordinaryProductDet t q))).mul_const s)
  have hJ : Integrable J μ := (hI s.re hs).mono' (hF.mul hPow.aestronglyMeasurable) (ae_of_all _ fun p => by
    change ‖F p * (ordinaryProductDet t q p : ℂ) ^ s‖ ≤ _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ordinaryProductDet_pos t q p)])
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace (KU n) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  let : SigmaFinite (complexSelfDualMeasure a).measure := inferInstance
  let : SigmaFinite (outerMeasure k q (complexSelfDualMeasure a) κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite (unitOuterMeasure k q (complexSelfDualMeasure a) κ) := SigmaFinite.withDensity _
  let : SigmaFinite η := sigmaFinite_ordinaryChartMeasure t q a κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : SigmaFinite (entryHaar (complexSelfDualMeasure a) (q + 1)) := entryHaar_sigmaFinite _ _
  let : SecondCountableTopology (Q t) := by
    let : SecondCountableTopology H :=
      (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) k).isInducing.secondCountableTopology
    exact TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (U k)).isOpenMap
  have hLead : Measurable (lead : Side → H) := by fun_prop
  let e := (quotientShift (U k) lead hLead).symm
  have he : MeasurePreserving e μ μ :=
    (measurePreserving_quotientShift (U k) D.measure η D.compatible.right_invariant lead hLead).symm _
  have hB_eq : J ∘ e = B := funext fun p => ordinaryKernel_shift t q a d T W V s p.1 p.2
  have hB : Integrable B μ := hB_eq ▸ he.integrable_comp_of_integrable hJ
  have hP (g : H) : P g (1 / 2) * P g (0 - (((t + 1 + (q + 1) - t : ℕ) : ℂ) / 2)) = P g (0 - MellinShift) := by
    rw [← detPower_add]
    congr 1
    rw [show t + 1 + (q + 1) - t = (q + 1) + 1 by omega]
    push_cast
    ring
  change (∫ x, complexUnequalIntegrand h' U₀ V.val s x ∂D.measure) = C * ∫ p, J p ∂μ
  calc
    _ = C * ∫ x, (∫ p, B (x, p) ∂η) ∂D.measure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hB.prod_right_ae] with x hx
      let g := x.out
      rw [complexUnequalIntegrand_eq_mul]
      change U₀ (padGL (Nat.succ_le_succ (Nat.le_of_lt h')) g) * V.val g *
        P g (0 - (((t + 1 + (q + 1) - t : ℕ) : ℂ) / 2)) * (quotientDetAbs x : ℂ) ^ s = _
      rw [hExact g]
      change _ = C * ∫ p, B (x, p) ∂(unitOuterMeasure k q (complexSelfDualMeasure a) κ).prod
        (entryHaar (complexSelfDualMeasure a) (q + 1))
      rw [integral_prod _ hx]
      simp only [B, ordinaryBeforeKernel]
      simp_rw [integral_mul_const]
      change _ = C * (((∫ p, ∫ Z, unitOrdinaryKernel k q a d T W.val g 0 p Z
        ∂entryHaar (complexSelfDualMeasure a) (q + 1) ∂unitOuterMeasure k q (complexSelfDualMeasure a) κ) * V.val g) *
        P g (0 - MellinShift) * (quotientDetAbs x : ℂ) ^ s)
      rw [← hP g]
      unfold C
      ring
    _ = C * ∫ p, J p ∂μ := by
      rw [← integral_prod _ hB, ← hB_eq]
      exact congrArg (C * ·) (he.integral_comp e.measurableEmbedding J)

end Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinarySeparation
