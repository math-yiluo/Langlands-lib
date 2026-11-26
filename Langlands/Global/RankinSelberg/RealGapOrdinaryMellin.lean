import Langlands.Global.RankinSelberg.RealGapNormalizedPowerMoment
import Langlands.Global.RankinSelberg.RealGapOrdinarySeparation
import Langlands.Global.RankinSelberg.RealGodementBlockUnfolding

/-! # The real ordinary zeta integral on the separated determinant chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapOrdinarySeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant rankInclusion weylLong)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap rightTranslate rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs realSelfDualMeasure
  realUnequalIntegrand realUnequalIntegral)
open ArchimedeanRealPairIdentity (ofReal_cpow_eq_exp)
open RealJacquet (realAdjacentMatrixWeight)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapAlternateWeighted (leadingSide ordinaryKernel_mk left_translate leftCharacter_of_mem)
open RealGapColumnFourier (columnSchwartzFourier)
open RealGapDualChart (retainedTail)
open RealGapLeadingFourier (leadingRestriction)
open RealGapNormalizedRestriction (unitOrdinaryKernel)
open RealGapNormalizedWeighted (realGapNormalizedPowerMoment padGL_eq_rankInclusion quotientDetAbs_mk)
open RealGapRankCoordinates (rankLT)
open RealGapSeparatedKernels (detPower_add retainedCoefficient unitOrdinaryKernel_separate)
open RealGapTriangularChart (Outer outerMeasure)
open RealGapUnitDeterminant (unitOuterMeasure)
open RealGapWeylRestriction (reverseTail)
open ComplexGodementBlockUnfolding (quotientShift measurePreserving_quotientShift)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealUnequalFamily (HasLeftCharacter)
open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs
  realUnequalIntegrand_eq_mul sigmaFinite_quotient)
open RealWhittakerTranslatedIntegrals (weightedOrdinary)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "ρ" => ArchimedeanLocal.translateFunction

local instance gapOrdinaryMellinGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapOrdinaryMellinGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapOrdinaryMellinGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapOrdinaryMellinGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapOrdinaryMellinUMeasurable (n : ℕ) : MeasurableSpace (U n) := borel _
local instance gapOrdinaryMellinUBorel (n : ℕ) : BorelSpace (U n) := ⟨rfl⟩
local instance gapOrdinaryMellinQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapOrdinaryMellinQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩
local instance gapOrdinaryMellinQSecondCountable (n : ℕ) : SecondCountableTopology (Q n) :=
  TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (U (n + 1))).isOpenMap

variable (t q : ℕ)
local notation "k" => t + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "Side" => Outer k q × U (q + 1)
local notation "Coords" => Q t × Side
local notation "h" => rankLT t q
local notation "h'" => rankLT t (q + 1)
local notation "lead" => fun p : Side => Prod.fst (Prod.fst (Prod.fst (Prod.fst p)))
local notation "MellinShift" => (((q + 1 : ℕ) : ℂ) / 2)

/-- The two determinant variables of the ordinary separated chart multiply to the zeta determinant. -/
def ordinaryProductDet (p : Coords) : ℝ := quotientDetAbs p.1 * δ (lead p.2)

/-- The product determinant is positive. -/
theorem ordinaryProductDet_pos (p : Coords) : 0 < ordinaryProductDet t q p :=
  mul_pos (quotientDetAbs_pos p.1) (abs_pos.mpr (lead p.2).det_ne_zero)

/-- The product determinant is measurable. -/
theorem measurable_ordinaryProductDet : Measurable (ordinaryProductDet t q) := by
  have hLead : Continuous (fun p : Coords => lead p.2) := by fun_prop
  exact (continuous_quotientDetAbs.comp continuous_fst).measurable.mul
    ((Units.continuous_val.comp hLead).matrix_det.abs).measurable

/-- The independent profiles multiply the separated kernel at unit profiles. -/
theorem ordinarySeparatedKernel_mul_profiles (dual : Bool) (a : ℝˣ) (c : RealCharacterData)
    (T : GodementColumnFactors k q) (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Coords) :
    ordinarySeparatedKernel t q dual a c T W V f₁ f₂ p =
      ordinarySeparatedKernel t q dual a c T W V (fun _ => 1) (fun _ => 1) p *
        (f₁ (quotientDetAbs p.1) * f₂ (δ (leadingSide dual (lead p.2)))) := by
  simp only [ordinarySeparatedKernel, weightedOrdinary, mul_one]
  ring

set_option maxHeartbeats 850000 in
/-- The unweighted chart kernel is a.e. strongly measurable and has all sufficiently large
absolute moments. -/
theorem ordinaryMellinData (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H)
    (κ : Measure (KU n)) (hη₁ : η₁.IsHaarMeasure) (hκ : κ.IsHaarMeasure) (c : RealCharacterData)
    (T : GodementColumnFactors k q) (ds es : List RealBlock) (W : G n → ℂ) (V : H → ℂ)
    (hW : W ∈ realUniformWhittakerModel r ds (-a)) (hV : V ∈ realUniformWhittakerModel t es a) :
    let μ := D.measure.prod (ordinaryChartMeasure t q a η₁ κ)
    let F := ordinarySeparatedKernel t q false a c T W V (fun _ => 1) (fun _ => 1)
    AEStronglyMeasurable F μ ∧ ∃ σ : ℝ, ∀ x : ℝ, σ ≤ x →
      Integrable (fun p => ‖F p‖ * ordinaryProductDet t q p ^ x) μ := by
  intro μ F
  let β := (c.exponent + (t : ℂ) / 2).re
  obtain ⟨b, hMoment⟩ := realGapNormalizedPowerMoment t q a D η₁ κ hη₁ hκ ds es W V hW hV β
  let σ := max 0 b
  have hWb (p : Outer k q) : ‖chartMultiplier t q false c p‖ ≤ δ p.1.1.1 ^ β := by
    rw [norm_chartMultiplier]
    rfl
  have hMoment' (z : ℝ) (hz : σ ≤ z) :
      Integrable (fun p => F p * ((ordinaryProductDet t q p ^ z : ℝ) : ℂ)) μ := by
    let f (x : ℝ) : ℂ := (x ^ z : ℝ)
    have hC : Integrable (comparisonChartKernel t q false a c T W V f f)
        (RealGapNormalizedWeighted.normalizedGapMeasure t q a D (comparisonRectangleMeasure t q false a)
          η₁ κ) :=
      hMoment z ((le_max_right _ _).trans hz) (rectangularLeading t q false a T) (T.tail (Fin.last (q + 1)))
        (columnSchwartzFourier a (T.tail 0)) ((reverseTail k q T).partial k q a).later
        (chartMultiplier t q false c) (measurable_chartMultiplier t q false c) hWb
    have hI := (realGapOrdinarySeparation t q D a η₁ κ hη₁ hκ false c T ds W hW V f f hC).1
    refine hI.congr (ae_of_all _ fun p => ?_)
    rw [ordinarySeparatedKernel_mul_profiles]
    have hy : 0 ≤ realNormalizedAbs (lead p.2).val.det := abs_nonneg _
    change F p * (((quotientDetAbs p.1 ^ z : ℝ) : ℂ) * ((realNormalizedAbs (lead p.2).val.det ^ z : ℝ) : ℂ)) =
      F p * (((quotientDetAbs p.1 * realNormalizedAbs (lead p.2).val.det) ^ z : ℝ) : ℂ)
    rw [← Complex.ofReal_mul, Real.mul_rpow (quotientDetAbs_pos p.1).le hy]
  have hσ : 0 ≤ σ := le_max_left _ _
  have hm : Measurable (fun p => (((ordinaryProductDet t q p ^ σ : ℝ) : ℂ))⁻¹) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_rpow_const hσ)).measurable.comp
      (measurable_ordinaryProductDet t q)).inv
  refine ⟨((hMoment' σ le_rfl).aestronglyMeasurable.mul hm.aestronglyMeasurable).congr
    (ae_of_all _ fun p => ?_), σ, fun z hz => ?_⟩
  · have hp : ((ordinaryProductDet t q p ^ σ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (ordinaryProductDet_pos t q p) σ).ne'
    change F p * ((ordinaryProductDet t q p ^ σ : ℝ) : ℂ) *
      ((ordinaryProductDet t q p ^ σ : ℝ) : ℂ)⁻¹ = F p
    rw [mul_assoc, mul_inv_cancel₀ hp, mul_one]
  · refine (hMoment' z hz).norm.congr (ae_of_all _ fun p => ?_)
    change ‖F p * ((ordinaryProductDet t q p ^ z : ℝ) : ℂ)‖ = _
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (ordinaryProductDet_pos t q p).le z)]

private def ordinaryBeforeKernel (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (s : ℂ) (p : Coords) : ℂ :=
  unitOrdinaryKernel k q a c T W p.1.out p.2.1 p.2.2 * V p.1.out *
    P p.1.out (0 - MellinShift) * (quotientDetAbs p.1 : ℂ) ^ s

set_option maxHeartbeats 1400000 in
private theorem ordinaryKernel_shift (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    {ds es : List RealBlock} (W : G n → ℂ) (V : H → ℂ)
    (hW : W ∈ realUniformWhittakerModel r ds (-a)) (hV : V ∈ realUniformWhittakerModel t es a)
    (s : ℂ) (x : Q t) (p : Side) :
    let v := (rightTranslate (U k) (lead p)⁻¹ x, p)
    ordinarySeparatedKernel t q false a c T W V (fun _ => 1) (fun _ => 1) v *
      (ordinaryProductDet t q v : ℂ) ^ s = ordinaryBeforeKernel t q a c T W V s (x, p) := by
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
    simp only [Units.val_mul, Matrix.det_mul, realNormalizedAbs, abs_mul]
  have hdet : ordinaryProductDet t q v = quotientDetAbs x := by
    rw [hv]
    change quotientDetAbs (Quotient.mk _ y : Q t) * δ z = δ g
    rw [quotientDetAbs_mk, ← hmul, show y * z = g from inv_mul_cancel_right g z]
  have hVl : HasLeftCharacter (-(-a)) (ρ z V) := by
    simpa only [neg_neg] using left_translate (leftCharacter_of_mem hV) z
  have hWl : HasLeftCharacter (-a) (ρ C⁻¹ W) := left_translate (leftCharacter_of_mem hW) C⁻¹
  have hpad : padGL (Nat.succ_le_succ (Nat.le_of_lt h)) y = rankInclusion (q + 1) y :=
    padGL_eq_rankInclusion k q y
  have hgap : r - t = q + 1 := by omega
  rw [hdet, hv]
  simp only [ordinarySeparatedKernel, weightedOrdinary, leadingSide, sideCharacter, squareLeading,
    Bool.false_eq_true, ite_false, mul_one]
  rw [ordinaryKernel_mk h hWl hVl, hpad, hgap]
  have hs := unitOrdinaryKernel_separate t q a c T W y p.1 p.2 0
  change P (y * z) (0 - MellinShift) * unitOrdinaryKernel k q a c T W (y * z) p.1 p.2 =
    retainedCoefficient t q a c T C * (W (rankInclusion (q + 1) y * C⁻¹) * P y (0 - MellinShift)) *
      realAdjacentMatrixWeight c.character.toMonoidHom (leadingRestriction k (q + 1) k C T.leading) 0 z at hs
  have hy : y * z = g := inv_mul_cancel_right g z
  rw [hy] at hs
  change retainedCoefficient t q a c T C *
      (W (rankInclusion (q + 1) y * C⁻¹) * V (y * z) * P y (0 - MellinShift)) *
      realAdjacentMatrixWeight c.character.toMonoidHom (leadingRestriction k (q + 1) k C T.leading) 0 z *
        (quotientDetAbs x : ℂ) ^ s = _
  rw [hy]
  calc
    _ = (retainedCoefficient t q a c T C * (W (rankInclusion (q + 1) y * C⁻¹) * P y (0 - MellinShift)) *
      realAdjacentMatrixWeight c.character.toMonoidHom (leadingRestriction k (q + 1) k C T.leading) 0 z) *
        V g * (quotientDetAbs x : ℂ) ^ s := by ring
    _ = _ := by rw [← hs]; unfold ordinaryBeforeKernel; dsimp only [g]; ring

/-- An exact ordinary restriction with one chart constant gives the exact Mellin identity on a
right half-plane. -/
def RealGapOrdinaryMellinStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H) (κ : Measure (KU n)),
    η₁.IsHaarMeasure → κ.IsHaarMeasure →
    ∀ (C : ℂ) (c : RealCharacterData) (T : GodementColumnFactors k q)
      (ds es : List RealBlock) (W : G n → ℂ) (V : H → ℂ),
      W ∈ realUniformWhittakerModel r ds (-a) → V ∈ realUniformWhittakerModel t es a →
    ∀ U₀ : G (n + 1) → ℂ,
    (∀ g : H, U₀ (padGL (Nat.succ_le_succ (Nat.le_of_lt h')) g) = P g (1 / 2) * C *
      ∫ p, (∫ Z, unitOrdinaryKernel k q a c T W g p Z ∂entryHaar (realSelfDualMeasure a) (q + 1))
        ∂unitOuterMeasure k q (realSelfDualMeasure a) η₁ κ) →
    let μ := D.measure.prod (ordinaryChartMeasure t q a η₁ κ)
    let F := ordinarySeparatedKernel t q false a c T W V (fun _ => 1) (fun _ => 1)
    AEStronglyMeasurable F μ ∧ ∃ σ : ℝ, ∀ s : ℂ, σ ≤ s.re →
      Integrable (fun p => ‖F p‖ * ordinaryProductDet t q p ^ s.re) μ ∧
      realUnequalIntegral h' D U₀ V s = C * ∫ p, F p * (ordinaryProductDet t q p : ℂ) ^ s ∂μ

set_option maxHeartbeats 1400000 in
theorem realGapOrdinaryMellin : RealGapOrdinaryMellinStatement t q := by
  intro D a η₁ κ hη₁ hκ C c T ds es W V hW hV U₀ hExact μ F
  obtain ⟨hF, σ, hI⟩ := ordinaryMellinData t q D a η₁ κ hη₁ hκ c T ds es W V hW hV
  refine ⟨hF, σ, fun s hs => ⟨hI s.re hs, ?_⟩⟩
  let η := ordinaryChartMeasure t q a η₁ κ
  let B := ordinaryBeforeKernel t q a c T W V s
  let J := fun p : Coords => F p * (ordinaryProductDet t q p : ℂ) ^ s
  have hPow : Measurable (fun p : Coords => (ordinaryProductDet t q p : ℂ) ^ s) := by
    simp_rw [ofReal_cpow_eq_exp (ordinaryProductDet_pos t q _)]
    exact Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp
        (Real.measurable_log.comp (measurable_ordinaryProductDet t q))).mul_const s)
  have hJ : Integrable J μ := (hI s.re hs).mono' (hF.mul hPow.aestronglyMeasurable) (ae_of_all _ fun p => by
    change ‖F p * (ordinaryProductDet t q p : ℂ) ^ s‖ ≤ _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ordinaryProductDet_pos t q p)])
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : (realSelfDualMeasure a).measure.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  let : SigmaFinite (realSelfDualMeasure a).measure := inferInstance
  let : SecondCountableTopology (KU n) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SigmaFinite (outerMeasure k q (realSelfDualMeasure a) η₁ κ) := by
    unfold outerMeasure; infer_instance
  let : SigmaFinite (unitOuterMeasure k q (realSelfDualMeasure a) η₁ κ) := SigmaFinite.withDensity _
  let : SigmaFinite η := sigmaFinite_ordinaryChartMeasure t q a η₁ κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : SigmaFinite (entryHaar (realSelfDualMeasure a) (q + 1)) := entryHaar_sigmaFinite _ _
  have hLead : Measurable (lead : Side → H) := by fun_prop
  let e := (quotientShift (U k) lead hLead).symm
  have he : MeasurePreserving e μ μ :=
    (measurePreserving_quotientShift (U k) D.measure η D.compatible.right_invariant lead hLead).symm _
  have hB_eq : J ∘ e = B := funext fun p => ordinaryKernel_shift t q a c T W V hW hV s p.1 p.2
  have hB : Integrable B μ := hB_eq ▸ he.integrable_comp_of_integrable hJ
  have hP (g : H) : P g (1 / 2) * P g (0 - (((t + 1 + (q + 1) - t : ℕ) : ℂ) / 2)) =
      P g (0 - MellinShift) := by
    rw [← detPower_add]
    congr 1
    rw [show t + 1 + (q + 1) - t = (q + 1) + 1 by omega]
    push_cast
    ring
  change (∫ x, realUnequalIntegrand h' U₀ V s x ∂D.measure) = C * ∫ p, J p ∂μ
  calc
    _ = C * ∫ x, (∫ p, B (x, p) ∂η) ∂D.measure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hB.prod_right_ae] with x hx
      let g := x.out
      rw [realUnequalIntegrand_eq_mul]
      change U₀ (padGL (Nat.succ_le_succ (Nat.le_of_lt h')) g) * V g *
        P g (0 - (((t + 1 + (q + 1) - t : ℕ) : ℂ) / 2)) * (quotientDetAbs x : ℂ) ^ s = _
      rw [hExact g]
      change _ = C * ∫ p, B (x, p) ∂(unitOuterMeasure k q (realSelfDualMeasure a) η₁ κ).prod
        (entryHaar (realSelfDualMeasure a) (q + 1))
      rw [integral_prod _ hx]
      simp only [B, ordinaryBeforeKernel]
      simp_rw [integral_mul_const]
      change _ = C * (((∫ p, ∫ Z, unitOrdinaryKernel k q a c T W g p Z
        ∂entryHaar (realSelfDualMeasure a) (q + 1) ∂unitOuterMeasure k q (realSelfDualMeasure a) η₁ κ) *
          V g) * P g (0 - MellinShift) * (quotientDetAbs x : ℂ) ^ s)
      rw [← hP g]
      ring
    _ = C * ∫ p, J p ∂μ := by
      rw [← integral_prod _ hB, ← hB_eq]
      exact congrArg (C * ·) (he.integral_comp e.measurableEmbedding J)

end Langlands.Global.RankinSelbergGlobal.RealGapOrdinarySeparation
