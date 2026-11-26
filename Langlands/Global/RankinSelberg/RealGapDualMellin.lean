import Langlands.Global.RankinSelberg.RealGapDualPowerMoment
import Langlands.Global.RankinSelberg.RealGapDualSeparation
import Langlands.Global.RankinSelberg.RealJacquetConventionReduction

/-! # The real dual zeta integral on the separated determinant chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapDualSeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose inverseTransposeContinuous)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (realNormalizedAbs realSelfDualMeasure RealQuotientMeasureData
  realUnequalDualKernel realUnequalDualIntegral)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapAlternateWeighted (leftCharacter_of_mem)
open RealGapDualHaar (dualChartMeasure sigmaFinite_dualChartMeasure dualChartWeightedKernel)
open RealGapDualPowerMoment (realGapDualPowerMoment)
open RealGapNormalizedRestriction (unitDualKernel)
open RealGapRankCoordinates (rankLT rectangleRows)
open RealGapSeparatedKernels (detPower_add)
open RealGapTriangularChart (Outer)
open RealUnequalFamily (HasLeftCharacter)
open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs
  realUnequalDualKernel_eq_mul sigmaFinite_quotient)
open RealWhittakerTranslatedIntegrals (weightedDual)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "SD" => realSelfDualMeasure

local instance gapDualMellinGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapDualMellinGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapDualMellinUMeasurable (n : ℕ) : MeasurableSpace (Unip n) := borel _
local instance gapDualMellinUBorel (n : ℕ) : BorelSpace (Unip n) := ⟨rfl⟩
local instance gapDualMellinQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapDualMellinQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "TailSize" => q + 1
local notation "Rank" => t + 1 + q + 1
local notation "H" => G Small
local notation "ι" => inverseTranspose Small ℝ
local notation "X" => M (t + 1 + (q + 1) - Small) Small
local notation "Chart" => Outer Small q × (M q Small × Unip TailSize)
local notation "Coords" => Q t × Chart
local notation "Joint" => Q t × (X × Chart)
local notation "Sq" => M Rank Rank
local notation "h'" => rankLT t (q + 1)
local notation "MellinShift" => (((q + 1 : ℕ) : ℂ) / 2)

/-- The second determinant variable of the separated dual chart. -/
def dualLeadingDet (p : Coords) : ℝ := δ (ι p.2.1.1.1.1)

/-- The second determinant variable is positive. -/
theorem dualLeadingDet_pos (p : Coords) : 0 < dualLeadingDet t q p :=
  abs_pos.mpr (ι p.2.1.1.1.1).det_ne_zero

/-- The second determinant variable is measurable. -/
theorem measurable_dualLeadingDet : Measurable (dualLeadingDet t q) := by
  have hLead : Continuous (fun p : Coords => ι p.2.1.1.1.1) :=
    (inverseTransposeContinuous Small ℝ).continuous.comp (by fun_prop)
  exact ((Units.continuous_val.comp hLead).matrix_det.abs).measurable

/-- The product determinant of the separated dual chart. -/
def dualProductDet (p : Coords) : ℝ := quotientDetAbs p.1 * dualLeadingDet t q p

/-- The product determinant is positive. -/
theorem dualProductDet_pos (p : Coords) : 0 < dualProductDet t q p :=
  mul_pos (quotientDetAbs_pos p.1) (dualLeadingDet_pos t q p)

/-- The product determinant is measurable. -/
theorem measurable_dualProductDet : Measurable (dualProductDet t q) :=
  (continuous_quotientDetAbs.measurable.comp measurable_fst).mul (measurable_dualLeadingDet t q)

/-- Multiplying by the two profiles gives the separated dual kernel from its unit-profile case. -/
theorem dualSeparatedKernel_mul_profiles (a : ℝˣ) (c : RealCharacterData)
    (T : GodementColumnFactors Small q) (W : G Rank → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Coords) :
    dualSeparatedKernel t q a c T W V f₁ f₂ p =
      dualSeparatedKernel t q a c T W V (fun _ => 1) (fun _ => 1) p *
        (f₁ (quotientDetAbs p.1) * f₂ (dualLeadingDet t q p)) := by
  simp only [dualSeparatedKernel, weightedDual, mul_one, dualLeadingDet]
  ring

private theorem dualChartPower_eq (a : ℝˣ) (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ))
    (T : GodementColumnFactors Small q) (Wd : G Rank → ℂ) (Vd : H → ℂ) (s : ℂ) (p : Joint) :
    let f (x : ℝ) := (x : ℂ) ^ s
    dualChartWeightedKernel t q a c Fs T Wd Vd f f p =
      unitDualKernel Small q a c Fs T Wd p.1.out (rectangleRows t TailSize p.2.1) p.2.2 * Vd p.1.out *
        P p.1.out (0 - MellinShift) * (quotientDetAbs p.1 : ℂ) ^ s := by
  intro f
  let x := quotientDetAbs p.1
  let y := δ (ι p.2.2.1.1.1.1)
  have hx : 0 < x := quotientDetAbs_pos p.1
  have hy : 0 < y := abs_pos.mpr (ι p.2.2.1.1.1.1).det_ne_zero
  have hpow : f (x * y⁻¹) * f y = (x : ℂ) ^ s := by
    change ((x * y⁻¹ : ℝ) : ℂ) ^ s * (y : ℂ) ^ s = _
    rw [← Complex.mul_cpow_ofReal_nonneg (mul_nonneg hx.le (inv_nonneg.mpr hy.le)) hy.le,
      ← Complex.ofReal_mul, mul_assoc, inv_mul_cancel₀ hy.ne', mul_one]
  unfold dualChartWeightedKernel
  dsimp only
  rw [mul_assoc _ (f (x * y⁻¹)) (f y), hpow]

/-- The separated real dual kernel has all sufficiently large absolute moments, and its Mellin
integral is the exact dual zeta integral after the constant of the exact restriction. -/
def RealGapDualMellinStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H) (κ : Measure (KU Rank)),
    η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∀ (C : ℂ) (c : RealCharacterData) (T : GodementColumnFactors Small q) (Fs : 𝓢(Sq, ℂ)),
      (∀ B, Fs B = T.squareEval Small q B) →
    ∀ (ds es dds ees : List RealBlock) (W : G Rank → ℂ) (V : H → ℂ) (U : G (Rank + 1) → ℂ),
      W ∈ realUniformWhittakerModel (t + 1 + q) ds (-a) → V ∈ realUniformWhittakerModel t es a →
      ArchimedeanLocal.dualFunction Rank W ∈ realUniformWhittakerModel (t + 1 + q) dds a →
      ArchimedeanLocal.dualFunction Small V ∈ realUniformWhittakerModel t ees (-a) →
    let Wd := ArchimedeanLocal.dualFunction Rank W
    let η := dualChartMeasure t q a η₁ κ
    (∀ (g : H) (x : X), ArchimedeanLocal.dualFunction (Rank + 1) U
        (ArchimedeanLocal.rectangularPoint h' g x * ArchimedeanLocal.unfoldingWeyl h') =
      P g (1 / 2) * C * (∫ y, unitDualKernel Small q a c Fs T Wd g (rectangleRows t TailSize x) y ∂η)) →
    let μ := D.measure.prod η
    let F := dualSeparatedKernel t q a c T W V (fun _ => 1) (fun _ => 1)
    AEStronglyMeasurable F μ ∧ ∃ σ : ℝ, ∀ s : ℂ, σ ≤ s.re →
      Integrable (fun p => ‖F p‖ * dualProductDet t q p ^ s.re) μ ∧
      realUnequalDualIntegral h' (-a) D U V s = C * ∫ p, F p * (dualProductDet t q p : ℂ) ^ s ∂μ

set_option maxHeartbeats 1200000 in
theorem realGapDualMellin : RealGapDualMellinStatement t q := by
  intro D a η₁ κ hη₁ hκ hκinv C c T Fs hT ds es dds ees W V U hWm hVm hWdm hVdm Wd η hExact μ F
  let Vd := ArchimedeanLocal.dualFunction Small V
  let ξ := rectangularMeasure (SD a) (Rank - Small) Small
  let ρ₀ := D.measure.prod (ξ.prod η)
  let J (s : ℂ) := fun p : Coords => F p * (dualProductDet t q p : ℂ) ^ s
  let K (s : ℂ) := dualChartWeightedKernel t q a c Fs T Wd Vd (fun x : ℝ => (x : ℂ) ^ s)
    (fun x : ℝ => (x : ℂ) ^ s)
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite η := sigmaFinite_dualChartMeasure t q a η₁ κ
  let : (SD a).measure.IsAddHaarMeasure := (SD a).isAddHaar
  let : ξ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ξ := inferInstance
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  obtain ⟨σ, hK⟩ := realGapDualPowerMoment t q D a η₁ κ hη₁ hκ hκinv dds ees Wd Vd hWdm hVdm c Fs T hT
  have hW : HasLeftCharacter (-a) W := leftCharacter_of_mem hWm
  have hV : HasLeftCharacter a V := leftCharacter_of_mem hVm
  have hSep (s : ℂ) (hs : σ ≤ s.re) : Integrable (J s) μ ∧ (∫ p, K s p ∂ρ₀) = ∫ p, J s p ∂μ := by
    let f (x : ℝ) := (x : ℂ) ^ s
    obtain ⟨hi, he⟩ := realGapDualSeparation t q D a η₁ κ hη₁ hκ c Fs T hT W V hW hV f f (hK s hs)
    have hpt (p : Coords) : dualSeparatedKernel t q a c T W V f f p = J s p := by
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
    have hPt (x : Q t) (y : X) : realUnequalDualKernel h' U V s (x, y) =
        C * ∫ u : Chart, K s (x, y, u) ∂η := by
      let g := x.out
      rw [realUnequalDualKernel_eq_mul]
      change ArchimedeanLocal.dualFunction (Rank + 1) U
          (ArchimedeanLocal.rectangularPoint h' g y * ArchimedeanLocal.unfoldingWeyl h') * Vd g *
        P g (0 - (((t + 1 + (q + 1) - t : ℕ) : ℂ) / 2)) * (quotientDetAbs x : ℂ) ^ s = _
      rw [hExact g y]
      have hKernel (u : Chart) : K s (x, y, u) =
          unitDualKernel Small q a c Fs T Wd g (rectangleRows t TailSize y) u * Vd g *
            P g (0 - MellinShift) * (quotientDetAbs x : ℂ) ^ s :=
        dualChartPower_eq t q a c Fs T Wd Vd s (x, y, u)
      simp_rw [hKernel, integral_mul_const]
      rw [← hP g]
      ring
    unfold realUnequalDualIntegral ArchimedeanLocal.blockIntegral
    rw [RealJacquet.selfDualMeasure_neg]
    change (∫ x, ∫ y, realUnequalDualKernel h' U V s (x, y) ∂ξ ∂D.measure) =
      C * ∫ p, J s p ∂μ
    rw [← (hSep s hs).2, integral_prod _ (hK s hs), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(hK s hs).prod_right_ae] with x hx
    rw [integral_prod _ hx, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (hPt x))

end Langlands.Global.RankinSelbergGlobal.RealGapDualSeparation
