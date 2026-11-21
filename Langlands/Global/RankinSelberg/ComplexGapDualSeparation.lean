import Langlands.Global.RankinSelberg.ComplexGapDualHaar
import Langlands.Global.RankinSelberg.ComplexGapLeadingHaar
import Langlands.Global.RankinSelberg.ComplexGapSeparatedKernels

/-! # Fubini and the quotient shear on the full dual chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapDualSeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose inverseTransposeContinuous rankInclusion determinant weylLong)
open Langlands.HarmonicAnalysis (rectangularJoin)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap rightTranslate rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexSelfDualMeasure
  complexUnequalIntegrand)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapDualChart (dualChart retainedTail)
open ComplexGapDualHaar (detAbs_mul detAbs_dualChart dualChartMeasure sigmaFinite_dualChartMeasure
  dualChartWeightedKernel dualChartWeightedKernel_eq lowerRectangle_eq_lowerShear)
open ComplexGapLeadingFourier (rectTransform)
open ComplexGapLeadingHaar (interchangeMiddle measurePreserving_interchangeMiddle)
open ComplexGapNormalizedRestriction (unitDualKernel)
open ComplexGapNormalizedWeighted (padGL_eq_rankInclusion quotientDetAbs_mk)
open ComplexGapOrdinaryWeighted (coupledHaarKernel)
open ComplexGapRankCoordinates (rankLT rectangleRows measurePreserving_rectangleRows)
open ComplexGapSeparatedKernels (retainedCoefficient unitDualKernel_separate translated_dualPoint)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest)
open ComplexGapTriangularChart (Outer)
open ComplexGodement (characterWeight)
open ComplexGodementBlockUnfolding (quotientShift measurePreserving_quotientShift)
open ComplexGodementLowerRectangle (lowerRectangle)
open ComplexGodementPaddedRestriction (paddedRestrictionKernel)
open ComplexGodementPartialFourier (partialSchwartz)
open ComplexAdjacentUnfolding (splitSquareTransform)
open ComplexTwoBlockHaar (diagonalBlocks_eq_padGL lastRow_diagonalBlocks_mul)
open ComplexUnequalFamily (HasLeftCharacter ordinaryKernel_mk dualKernel_mk dual_left_mul)
open ComplexUnequalMellinReduction (quotientDetAbs sigmaFinite_quotient)
open ComplexWhittakerTranslatedIntegrals (weightedDual)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "μ" => complexSelfDualMeasure
local notation "ρ" => ArchimedeanLocal.translateFunction

variable (t q : ℕ)
local notation "k" => t + 1
local notation "m" => q + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "X" => M (n - k) k
local notation "U" => M q k
local notation "Chart" => Outer k q × (U × N m)
local notation "Joint" => Q t × (X × Chart)
local notation "ι₁" => inverseTranspose k ℂ
local notation "Test" => 𝓢(M n (n + 1), ℂ)
local notation "gap" => (((q + 1 : ℕ) : ℂ) / 2)

private theorem left_translate {l : ℕ} {a : ℂˣ} {W : G (l + 1) → ℂ}
    (hW : HasLeftCharacter a W) (g : G (l + 1)) : HasLeftCharacter a (ρ g W) := by
  intro u y
  change W ((u.val * y) * g) = _
  rw [mul_assoc, hW]
  rfl

private theorem dualChartWeightedKernel_mk (a : ℂˣ) (d : ComplexCharacterData) (Φ : Test)
    (Wd : G n → ℂ) (Vd : H → ℂ) (hWd : HasLeftCharacter a Wd) (hVd : HasLeftCharacter (-a) Vd)
    (f₁ f₂ : ℝ → ℂ) (g : H) (x : X) (p : Chart) :
    let z := ι₁ p.1.1.1.1
    dualChartWeightedKernel t q a d Φ Wd Vd 0 f₁ f₂ (Quotient.mk _ g, x, p) =
      unitDualKernel k q a d Φ Wd g 0 (rectangleRows t m x) p * Vd g * P g (0 - gap) *
        f₁ (δ g * (δ z)⁻¹) * f₂ (δ z) := by
  intro z
  let C := dualChart k q p
  let h := rankLT t q
  have hL : HasLeftCharacter a (ρ C⁻¹ Wd) := left_translate hWd C⁻¹
  have hpad (g : H) : padGL (Nat.succ_le_succ h.le) g = rankInclusion m g :=
    padGL_eq_rankInclusion k q g
  have hrow : (padGL (Nat.succ_le_succ h.le) g * C⁻¹).val (Fin.last r) = C⁻¹.val (Fin.last r) := by
    rw [← diagonalBlocks_eq_padGL (Nat.succ_pos t) (Nat.succ_lt_succ h)]
    exact lastRow_diagonalBlocks_mul (Nat.succ_pos t) (Nat.succ_lt_succ h) g C⁻¹
  rw [← dualChartWeightedKernel_eq]
  unfold coupledHaarKernel
  dsimp only [Prod.fst, Prod.snd]
  change _ * _ * complexUnequalIntegrand h (ρ C⁻¹ Wd) Vd 0 (Quotient.mk _ g) *
    f₁ (quotientDetAbs (Quotient.mk _ g : Q t) * (δ C)⁻¹) * f₂ (δ C) = _
  rw [ordinaryKernel_mk h hL hVd, quotientDetAbs_mk, detAbs_dualChart,
    lowerRectangle_eq_lowerShear]
  unfold unitDualKernel ComplexGapMatchedTests.dualFiber paddedRestrictionKernel
  let χ := characterWeight d.inv (((r + 2 : ℕ) : ℂ) / 2 + (-0) - 1) (determinant C)
  change partialSchwartz (-a) (μ a) (rectTransform a Φ)
    (rectangularJoin (C.val * (ComplexGapDualChart.lowerShear k q (rectangleRows t m x)).val)
      (C⁻¹.val (Fin.last r))) * χ *
      (Wd (padGL (Nat.succ_le_succ h.le) g * C⁻¹) * Vd g * P g (0 - (((r - t : ℕ) : ℂ) / 2))) *
      f₁ (δ g * (δ z)⁻¹) * f₂ (δ z) = partialSchwartz (-a) (μ a) (rectTransform a Φ)
    (rectangularJoin (C.val * (ComplexGapDualChart.lowerShear k q (rectangleRows t m x)).val)
      ((rankInclusion m g * C⁻¹).val (Fin.last r))) *
      Wd (rankInclusion m g * C⁻¹) * χ *
      Vd g * P g (0 - gap) * f₁ (δ g * (δ z)⁻¹) * f₂ (δ z)
  rw [← hpad g, hrow, show r - t = q + 1 by omega]
  ring

/-- The separated dual kernel after the full rectangle integration. -/
def dualSeparatedKernel (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Q t × Chart) : ℂ :=
  let z := p.2.1.1.1.1
  let C := retainedTail k q p.2.1 p.2.2.2
  let Ξ := leadingSquareTest t q C T.leading
  let x := (rectangleRows t q).symm p.2.2.1
  (d.inv.character (determinant (weylLong m ℂ)) : ℂ) * retainedCoefficient t q a d T C *
    weightedDual (rankLT t q) (ρ C⁻¹ W) (ρ z V) f₁ (p.1, x) *
    squareKernel d.inv (splitSquareTransform a Ξ) (fun _ => 1) 0 (ι₁ z) * f₂ (δ (ι₁ z))

private theorem integrate_full_rectangle (a : ℂˣ) (d : ComplexCharacterData) (Φ : Test)
    (T : GodementColumnFactors k q) (hT : ∀ x, Φ x = T.eval k q x)
    (W : G n → ℂ) (V : H → ℂ) (hW : HasLeftCharacter (-a) W) (hV : HasLeftCharacter a V)
    (f₁ f₂ : ℝ → ℂ) (u : Q t) (p : Chart) :
    let z := ι₁ p.1.1.1.1
    let Xμ := rectangularMeasure (μ a) (n - k) k
    (∫ x : X, dualChartWeightedKernel t q a d Φ (ArchimedeanLocal.dualFunction n W) (ArchimedeanLocal.dualFunction k V) 0 f₁ f₂
      (rightTranslate (N k) z u, x, p) ∂Xμ) = dualSeparatedKernel t q a d T W V f₁ f₂ (u, p) := by
  intro z Xμ
  let Wd := ArchimedeanLocal.dualFunction n W
  let Vd := ArchimedeanLocal.dualFunction k V
  let C := retainedTail k q p.1 p.2.2
  let e := rectangleRows t m
  let η := rectangularMeasure (μ a) m k
  let h := p.1.1.1.1
  have hz : 0 < δ z := pow_pos (norm_pos_iff.mpr z.det_ne_zero) _
  have hWd : HasLeftCharacter a Wd := by
    intro u g
    simpa only [neg_neg] using dual_left_mul hW u g
  have hVd : HasLeftCharacter (-a) Vd := dual_left_mul hV
  induction u using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk]
    change (∫ x : X, dualChartWeightedKernel t q a d Φ Wd Vd 0 f₁ f₂
      (Quotient.mk _ (g * z), x, p) ∂Xμ) = _
    have hkernel (x : X) := dualChartWeightedKernel_mk t q a d Φ Wd Vd hWd hVd f₁ f₂ (g * z) x p
    dsimp only at hkernel
    simp_rw [hkernel]
    have hcancel : δ (g * z) * (δ z)⁻¹ = δ g := by
      rw [detAbs_mul, mul_assoc, mul_inv_cancel₀ hz.ne', mul_one]
    change (∫ x : X, unitDualKernel k q a d Φ Wd (g * z) 0 (e x) p * Vd (g * z) *
      P (g * z) (0 - gap) * f₁ (δ (g * z) * (δ z)⁻¹) * f₂ (δ z) ∂Xμ) = _
    rw [hcancel]
    simp_rw [integral_mul_const]
    have hMP : MeasurePreserving e Xμ η := measurePreserving_rectangleRows t m (μ a)
    have hInt : (∫ x : X, unitDualKernel k q a d Φ Wd (g * z) 0 (e x) p ∂Xμ) =
        ∫ x : M m k, unitDualKernel k q a d Φ Wd (g * z) 0 x p ∂η :=
      hMP.integral_comp' (fun x => unitDualKernel k q a d Φ Wd (g * z) 0 x p)
    rw [hInt, mul_right_comm _ (Vd (g * z)) (P (g * z) (0 - gap)), mul_comm _ (P (g * z) (0 - gap))]
    have hsep := unitDualKernel_separate t q a d Φ T hT Wd g p.1 p.2.2 p.2.1 0 0
    dsimp only at hsep
    simp only [neg_zero, add_zero] at hsep
    change P (g * z) (0 - gap) * (∫ x : M m k, unitDualKernel k q a d Φ Wd (g * z) 0 x p ∂η) = _ at hsep
    rw [hsep]
    unfold dualSeparatedKernel weightedDual
    dsimp only [Prod.fst, Prod.snd]
    have hVt : HasLeftCharacter (-(-a)) (ρ h V) := by simpa only [neg_neg] using left_translate hV h
    rw [dualKernel_mk (rankLT t q) (left_translate hW C⁻¹) hVt, quotientDetAbs_mk,
      translated_dualPoint, MeasurableEquiv.apply_symm_apply, show r - t = q + 1 by omega]
    have hVtranslate : ArchimedeanLocal.dualFunction k (ρ h V) g = Vd (g * z) := by
      unfold Vd ArchimedeanLocal.dualFunction ArchimedeanLocal.translateFunction
      simp only [map_mul, mul_assoc, z, h, Langlands.GeneralLinear.inverseTranspose_involutive]
    rw [hVtranslate]
    dsimp only [z, C, Wd, h]
    ring

/-- The dual Haar and rectangle integration can be replaced by the separated dual kernel. -/
def ComplexGapDualSeparationStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU n)), κ.IsHaarMeasure →
    ∀ (d : ComplexCharacterData) (Φ : Test) (T : GodementColumnFactors k q), (∀ x, Φ x = T.eval k q x) →
    ∀ (W : G n → ℂ) (V : H → ℂ), HasLeftCharacter (-a) W → HasLeftCharacter a V →
    ∀ (f₁ f₂ : ℝ → ℂ),
    let A := D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a κ))
    let B := D.measure.prod (dualChartMeasure t q a κ)
    let F := dualChartWeightedKernel t q a d Φ (ArchimedeanLocal.dualFunction n W) (ArchimedeanLocal.dualFunction k V) 0 f₁ f₂
    let Fs := dualSeparatedKernel t q a d T W V f₁ f₂
    Integrable F A → Integrable Fs B ∧ (∫ p, F p ∂A) = ∫ p, Fs p ∂B

set_option maxHeartbeats 1200000 in
theorem complexGapDualSeparation : ComplexGapDualSeparationStatement t q := by
  intro D a κ hκ d Φ T hT W V hW hV f₁ f₂
  dsimp only
  intro hF
  let A := D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a κ))
  let ξ := rectangularMeasure (μ a) (n - k) k
  let η := dualChartMeasure t q a κ
  let F := dualChartWeightedKernel t q a d Φ (ArchimedeanLocal.dualFunction n W) (ArchimedeanLocal.dualFunction k V) 0 f₁ f₂
  let Fs := dualSeparatedKernel t q a d T W V f₁ f₂
  let : κ.IsHaarMeasure := hκ
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : ξ.IsAddHaarMeasure := rectangularMeasure_isAddHaar (μ a) _ _
  let : SigmaFinite ξ := inferInstance
  let : SigmaFinite η := sigmaFinite_dualChartMeasure t q a κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : SecondCountableTopology (Q t) := by
    let : SecondCountableTopology H :=
      (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) k).isInducing.secondCountableTopology
    exact TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (N k)).isOpenMap
  let lead (p : X × Chart) := ι₁ p.2.1.1.1.1
  have hl : Measurable lead := (inverseTransposeContinuous k ℂ).continuous.measurable.comp (by fun_prop)
  let shift := quotientShift (N k) lead hl
  have hshift : MeasurePreserving shift A A :=
    measurePreserving_quotientShift (N k) D.measure (ξ.prod η) D.compatible.right_invariant lead hl
  let e := interchangeMiddle (A := Q t) (B := X) (C := Chart)
  have he : MeasurePreserving e ((D.measure.prod η).prod ξ) A :=
    measurePreserving_interchangeMiddle D.measure ξ η
  let J := F ∘ shift ∘ e
  have hJ : Integrable J ((D.measure.prod η).prod ξ) :=
    he.integrable_comp_of_integrable (hshift.integrable_comp_of_integrable hF)
  have hpt (p : Q t × Chart) : (∫ x : X, J (p, x) ∂ξ) = Fs p :=
    integrate_full_rectangle t q a d Φ T hT W V hW hV f₁ f₂ p.1 p.2
  change Integrable Fs (D.measure.prod η) ∧ (∫ p, F p ∂A) = ∫ p, Fs p ∂D.measure.prod η
  refine ⟨hJ.integral_prod_left.congr (ae_of_all _ hpt), ?_⟩
  calc
    _ = ∫ p, (F ∘ shift) p ∂A := (hshift.integral_comp shift.measurableEmbedding F).symm
    _ = ∫ p, J p ∂(D.measure.prod η).prod ξ := (he.integral_comp e.measurableEmbedding (F ∘ shift)).symm
    _ = ∫ p, Fs p ∂D.measure.prod η := (integral_prod J hJ).trans (integral_congr_ae (ae_of_all _ hpt))

end Langlands.Global.RankinSelbergGlobal.ComplexGapDualSeparation
