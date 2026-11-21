import Langlands.Global.RankinSelberg.ComplexGapDualPowerMoment
import Langlands.Global.RankinSelberg.ComplexGapDualSeparation

/-! # The dual zeta integral on the separated determinant chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapDualSeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose inverseTransposeContinuous)
open Langlands.GodementJacquet (complexNormalizedAbs_det_pos complexSelfDualMeasure_neg_scale)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure ComplexQuotientMeasureData
  complexUnequalDualKernel complexUnequalDualIntegral)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapDualHaar (dualChartMeasure sigmaFinite_dualChartMeasure dualChartWeightedKernel)
open ComplexGapDualPowerMoment (complexGapDualPowerMoment)
open ComplexGapNormalizedRestriction (unitDualKernel)
open ComplexGapRankCoordinates (rankLT rectangleRows)
open ComplexGapSeparatedKernels (detPower_add)
open ComplexGapTriangularChart (Outer)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)
open ComplexUnequalFamily (HasLeftCharacter)
open ComplexUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs
  complexUnequalDualKernel_eq_mul sigmaFinite_quotient)
open ComplexWhittakerTranslatedIntegrals (weightedDual)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "SD" => complexSelfDualMeasure

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "TailSize" => q + 1
local notation "Rank" => t + 1 + q + 1
local notation "H" => G Small
local notation "ι" => inverseTranspose Small ℂ
local notation "X" => M (t + 1 + (q + 1) - Small) Small
local notation "Chart" => Outer Small q × (M q Small × Unip TailSize)
local notation "Coords" => Q t × Chart
local notation "Joint" => Q t × (X × Chart)
local notation "Rect" => M Rank (Rank + 1)
local notation "h'" => rankLT t (q + 1)
local notation "MellinShift" => (((q + 1 : ℕ) : ℂ) / 2)

/-- The second determinant variable of the separated dual chart. -/
def dualLeadingDet (p : Coords) : ℝ := δ (ι p.2.1.1.1.1)

theorem dualLeadingDet_pos (p : Coords) : 0 < dualLeadingDet t q p := complexNormalizedAbs_det_pos _

theorem measurable_dualLeadingDet : Measurable (dualLeadingDet t q) := by
  have hLead : Continuous (fun p : Coords => ι p.2.1.1.1.1) :=
    (inverseTransposeContinuous Small ℂ).continuous.comp (by fun_prop)
  exact ((Units.continuous_val.comp hLead).matrix_det.norm.pow 2).measurable

/-- The product determinant of the separated dual chart. -/
def dualProductDet (p : Coords) : ℝ := quotientDetAbs p.1 * dualLeadingDet t q p

theorem dualProductDet_pos (p : Coords) : 0 < dualProductDet t q p :=
  mul_pos (quotientDetAbs_pos p.1) (dualLeadingDet_pos t q p)

theorem measurable_dualProductDet : Measurable (dualProductDet t q) :=
  (continuous_quotientDetAbs.measurable.comp measurable_fst).mul (measurable_dualLeadingDet t q)

/-- Multiplying by the two profiles gives the separated dual kernel from its unit-profile case. -/
theorem dualSeparatedKernel_mul_profiles (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors Small q)
    (W : G Rank → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Coords) :
    dualSeparatedKernel t q a d T W V f₁ f₂ p =
      dualSeparatedKernel t q a d T W V (fun _ => 1) (fun _ => 1) p *
        (f₁ (quotientDetAbs p.1) * f₂ (dualLeadingDet t q p)) := by
  simp only [dualSeparatedKernel, weightedDual, mul_one, dualLeadingDet]
  ring

private theorem dualChartPower_eq (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
    (Wd : G Rank → ℂ) (Vd : H → ℂ) (s : ℂ) (p : Joint) :
    let f (x : ℝ) := (x : ℂ) ^ s
    dualChartWeightedKernel t q a d Φ Wd Vd 0 f f p =
      unitDualKernel Small q a d Φ Wd p.1.out 0 (rectangleRows t TailSize p.2.1) p.2.2 * Vd p.1.out *
        P p.1.out (0 - MellinShift) * (quotientDetAbs p.1 : ℂ) ^ s := by
  intro f
  let x := quotientDetAbs p.1
  let y := δ (ι p.2.2.1.1.1.1)
  have hx : 0 < x := quotientDetAbs_pos p.1
  have hy : 0 < y := complexNormalizedAbs_det_pos _
  have hpow : f (x * y⁻¹) * f y = (x : ℂ) ^ s := by
    change ((x * y⁻¹ : ℝ) : ℂ) ^ s * (y : ℂ) ^ s = _
    rw [← Complex.mul_cpow_ofReal_nonneg (mul_nonneg hx.le (inv_nonneg.mpr hy.le)) hy.le,
      ← Complex.ofReal_mul, mul_assoc, inv_mul_cancel₀ hy.ne', mul_one]
  unfold dualChartWeightedKernel
  dsimp only
  rw [mul_assoc _ (f (x * y⁻¹)) (f y), hpow]

/-- The separated dual kernel has all sufficiently large absolute moments, and its Mellin
integral is the exact dual zeta integral after the common Haar scalar. -/
def ComplexGapDualMellinStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU Rank)), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∀ (c : ℝ≥0) (d : ComplexCharacterData) (T : GodementColumnFactors Small q) (Φ : 𝓢(Rect, ℂ)),
      (∀ x, Φ x = T.eval Small q x) →
    ∀ (ds es : List ComplexCharacterData), ds.length = Rank → es.length = Small →
    ∀ (W : complexWhittakerModel (t + 1 + q) ds (-a)) (V : complexWhittakerModel t es a)
      (U : G (Rank + 1) → ℂ),
    let Wd := ArchimedeanLocal.dualFunction Rank W.val
    let η := dualChartMeasure t q a κ
    (∀ (g : H) (x : X), ArchimedeanLocal.dualFunction (Rank + 1) U
        (ArchimedeanLocal.rectangularPoint h' g x * ArchimedeanLocal.unfoldingWeyl h') =
      P g (1 / 2) * (c : ℂ) * (∫ y, unitDualKernel Small q a d Φ Wd g 0 (rectangleRows t TailSize x) y ∂η)) →
    let μ := D.measure.prod η
    let F := dualSeparatedKernel t q a d T W.val V.val (fun _ => 1) (fun _ => 1)
    AEStronglyMeasurable F μ ∧ ∃ σ : ℝ, ∀ s : ℂ, σ ≤ s.re →
      Integrable (fun p => ‖F p‖ * dualProductDet t q p ^ s.re) μ ∧
      complexUnequalDualIntegral h' (-a) D U V.val s =
        (c : ℂ) * ∫ p, F p * (dualProductDet t q p : ℂ) ^ s ∂μ

set_option maxHeartbeats 1200000 in
theorem complexGapDualMellin : ComplexGapDualMellinStatement t q := by
  intro D a κ hκ hκinv c d T Φ hΦ ds es hds hes W V U Wd η hExact μ F
  let W' : complexWhittakerModel (t + 1 + q) (dualData ds) a :=
    ⟨Wd, by simpa only [Wd, neg_neg] using dualFunction_mem hds W.2⟩
  let Vd := ArchimedeanLocal.dualFunction Small V.val
  let V' : complexWhittakerModel t (dualData es) (-a) := ⟨Vd, dualFunction_mem hes V.2⟩
  let ξ := rectangularMeasure (SD a) (Rank - Small) Small
  let ρ₀ := D.measure.prod (ξ.prod η)
  let J (s : ℂ) := fun p : Coords => F p * (dualProductDet t q p : ℂ) ^ s
  let K (s : ℂ) := dualChartWeightedKernel t q a d Φ Wd Vd 0 (fun x : ℝ => (x : ℂ) ^ s) (fun x : ℝ => (x : ℂ) ^ s)
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite η := sigmaFinite_dualChartMeasure t q a κ
  let : ξ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ξ := inferInstance
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  obtain ⟨σ, hK⟩ := complexGapDualPowerMoment t q D a κ hκ hκinv _ _ W' V' d Φ T hΦ
  have hW : HasLeftCharacter (-a) W.val := fun u g => complexWhittakerModel_left_equivariant W.2 u.val u.2 g
  have hV : HasLeftCharacter a V.val := fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g
  have hSep (s : ℂ) (hs : σ ≤ s.re) : Integrable (J s) μ ∧ (∫ p, K s p ∂ρ₀) = ∫ p, J s p ∂μ := by
    let f (x : ℝ) := (x : ℂ) ^ s
    obtain ⟨hi, he⟩ := complexGapDualSeparation t q D a κ hκ d Φ T hΦ W.val V.val hW hV f f (hK s hs)
    have hpt (p : Coords) : dualSeparatedKernel t q a d T W.val V.val f f p = J s p := by
      rw [dualSeparatedKernel_mul_profiles]
      change F p * ((quotientDetAbs p.1 : ℂ) ^ s * (dualLeadingDet t q p : ℂ) ^ s) =
        F p * (dualProductDet t q p : ℂ) ^ s
      rw [← Complex.mul_cpow_ofReal_nonneg (quotientDetAbs_pos p.1).le (dualLeadingDet_pos t q p).le,
        ← Complex.ofReal_mul]
      rfl
    exact ⟨hi.congr (ae_of_all _ hpt), he.trans (integral_congr_ae (ae_of_all _ hpt))⟩
  have hBase : AEStronglyMeasurable F μ := by
    have hM : Measurable (fun p : Coords => ((dualProductDet t q p : ℂ) ^ (σ : ℂ))⁻¹) :=
      ((Complex.measurable_ofReal.comp (measurable_dualProductDet t q)).pow_const _).inv
    refine ((hSep (σ : ℂ) (by simp)).1.aestronglyMeasurable.mul hM.aestronglyMeasurable).congr
      (ae_of_all _ fun p => ?_)
    have hp : ((dualProductDet t q p : ℂ) ^ (σ : ℂ)) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (dualProductDet_pos t q p).ne'))
    change F p * ((dualProductDet t q p : ℂ) ^ (σ : ℂ)) * ((dualProductDet t q p : ℂ) ^ (σ : ℂ))⁻¹ = F p
    rw [mul_assoc, mul_inv_cancel₀ hp, mul_one]
  refine ⟨hBase, σ, fun s hs => ⟨?_, ?_⟩⟩
  · refine (hSep s hs).1.norm.congr (ae_of_all _ fun p => ?_)
    change ‖F p * (dualProductDet t q p : ℂ) ^ s‖ = _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (dualProductDet_pos t q p)]
  · have hP (g : H) : P g (1 / 2) * P g (0 - (((t + 1 + (q + 1) - t : ℕ) : ℂ) / 2)) =
        P g (0 - MellinShift) := by
      rw [← detPower_add]
      congr 1
      rw [show t + 1 + (q + 1) - t = (q + 1) + 1 by omega]
      push_cast
      ring
    have hPt (x : Q t) (y : X) : complexUnequalDualKernel h' U V.val s (x, y) =
        (c : ℂ) * ∫ u : Chart, K s (x, y, u) ∂η := by
      let g := x.out
      rw [complexUnequalDualKernel_eq_mul]
      change ArchimedeanLocal.dualFunction (Rank + 1) U
          (ArchimedeanLocal.rectangularPoint h' g y * ArchimedeanLocal.unfoldingWeyl h') * Vd g *
        P g (0 - (((t + 1 + (q + 1) - t : ℕ) : ℂ) / 2)) * (quotientDetAbs x : ℂ) ^ s = _
      rw [hExact g y]
      have hKernel (u : Chart) : K s (x, y, u) =
          unitDualKernel Small q a d Φ Wd g 0 (rectangleRows t TailSize y) u * Vd g *
            P g (0 - MellinShift) * (quotientDetAbs x : ℂ) ^ s :=
        dualChartPower_eq t q a d Φ Wd Vd s (x, y, u)
      simp_rw [hKernel, integral_mul_const]
      rw [← hP g]
      ring
    unfold complexUnequalDualIntegral ArchimedeanLocal.blockIntegral
    rw [complexSelfDualMeasure_neg_scale]
    change (∫ x, ∫ y, complexUnequalDualKernel h' U V.val s (x, y) ∂ξ ∂D.measure) =
      (c : ℂ) * ∫ p, J s p ∂μ
    rw [← (hSep s hs).2, integral_prod _ (hK s hs), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(hK s hs).prod_right_ae] with x hx
    rw [integral_prod _ hx, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (hPt x))

end Langlands.Global.RankinSelbergGlobal.ComplexGapDualSeparation
