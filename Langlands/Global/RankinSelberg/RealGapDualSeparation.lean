import Langlands.Global.RankinSelberg.RealGapDualHaar
import Langlands.Global.RankinSelberg.RealGapLeadingHaar
import Langlands.Global.RankinSelberg.RealGapSeparatedKernels
import Langlands.Global.RankinSelberg.RealGapAlternateWeighted
import Langlands.Global.RankinSelberg.RealGodementBlockUnfolding
import Langlands.Global.RankinSelberg.RealUnequalDualFamily
import Langlands.Global.RankinSelberg.RealWhittakerTranslatedIntegrals

/-! # Fubini and the quotient shear on the full real dual chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapDualSeparation

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose inverseTransposeContinuous rankInclusion determinant weylLong)
open Langlands.LocalFactor.Archimedean (RealCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap rightTranslate rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs realSelfDualMeasure realUnequalIntegrand)
open RealJacquet (realAdjacentMatrixWeight detCharacter)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapAlternateWeighted (ordinaryKernel_mk left_translate)
open RealGapDualChart (dualChart retainedTail)
open RealGapDualHaar (detAbs_mul detAbs_dualChart dualChartMeasure sigmaFinite_dualChartMeasure
  dualChartWeightedKernel dualChartWeightedKernel_eq lowerRectangle_eq_lowerShear)
open RealGapLeadingFourier (leadingRestriction)
open RealGapLeadingHaar (interchangeMiddle measurePreserving_interchangeMiddle)
open RealGapNormalizedRestriction (unitDualKernel)
open RealGapNormalizedWeighted (padGL_eq_rankInclusion quotientDetAbs_mk)
open RealGapOrdinaryWeighted (coupledHaarKernel)
open RealGapRankCoordinates (rankLT rectangleRows measurePreserving_rectangleRows)
open RealGapSeparatedKernels (retainedCoefficient unitDualKernel_separate translated_dualPoint)
open RealGapTriangularChart (Outer)
open ComplexGodementBlockUnfolding (quotientShift measurePreserving_quotientShift)
open RealGodementPaddedRestriction (paddedRestrictionKernel)
open RealTwoBlockHaar (diagonalBlocks_eq_padGL lastRow_diagonalBlocks_mul)
open RealUnequalFamily (HasLeftCharacter dualKernel_mk)
open RealUnequalMellinReduction (quotientDetAbs sigmaFinite_quotient)
open RealWhittakerTranslatedIntegrals (weightedDual)
open RealGodement (realRectangularSchwartzFourier realRowSchwartzFourier)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "μ" => realSelfDualMeasure
local notation "ρ" => ArchimedeanLocal.translateFunction

local instance gapDualSeparationGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapDualSeparationGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapDualSeparationGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapDualSeparationGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapDualSeparationUMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance gapDualSeparationUBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩
local instance gapDualSeparationQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapDualSeparationQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩
local instance gapDualSeparationQSecondCountable (n : ℕ) : SecondCountableTopology (Q n) :=
  TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (N (n + 1))).isOpenMap

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
local notation "ι₁" => inverseTranspose k ℝ
local notation "Sq" => M n n
local notation "gap" => (((q + 1 : ℕ) : ℂ) / 2)

private theorem detPower_eq_exp_logDet {l : ℕ} (g : G (l + 1)) (s : ℂ) :
    P g s = Complex.exp (s * (RealEqualConvergence.logDet g : ℂ)) := rfl

private theorem dualChartWeightedKernel_mk (a : ℝˣ) (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ))
    (T : GodementColumnFactors k q) (Wd : G n → ℂ) (Vd : H → ℂ) (hWd : HasLeftCharacter a Wd)
    (hVd : HasLeftCharacter (-a) Vd) (f₁ f₂ : ℝ → ℂ) (g : H) (x : X) (p : Chart) :
    let z := ι₁ p.1.1.1.1
    dualChartWeightedKernel t q a c Fs T Wd Vd f₁ f₂ (Quotient.mk _ g, x, p) =
      unitDualKernel k q a c Fs T Wd g (rectangleRows t m x) p * Vd g * P g (0 - gap) *
        f₁ (δ g * (δ z)⁻¹) * f₂ (δ z) := by
  intro z
  let C := dualChart k q p
  let h := rankLT t q
  have hL : HasLeftCharacter a (ρ C⁻¹ Wd) := left_translate hWd C⁻¹
  have hpad (g : H) : padGL (Nat.succ_le_succ h.le) g = rankInclusion m g :=
    padGL_eq_rankInclusion k q g
  have hrow : Langlands.RankinSelberg.lastRow (padGL (Nat.succ_le_succ h.le) g * C⁻¹) =
      Langlands.RankinSelberg.lastRow C⁻¹ := by
    rw [← diagonalBlocks_eq_padGL (Nat.succ_pos t) (Nat.succ_lt_succ h)]
    exact lastRow_diagonalBlocks_mul (Nat.succ_pos t) (Nat.succ_lt_succ h) g C⁻¹
  rw [← dualChartWeightedKernel_eq]
  unfold coupledHaarKernel
  dsimp only [Prod.fst, Prod.snd]
  have hD := detAbs_dualChart t q p
  dsimp only at hD
  rw [ordinaryKernel_mk h hL hVd, quotientDetAbs_mk, hD, lowerRectangle_eq_lowerShear]
  unfold unitDualKernel RealGapMatchedTests.dualFiber paddedRestrictionKernel
  have hC : RealGapDualArguments.dualMatrix k q (retainedTail k q p.1 p.2.2) p.1.1.1.1 p.2.1 = C := rfl
  rw [hC, ← hpad g, hrow, show r - t = q + 1 by omega]
  unfold ArchimedeanLocal.translateFunction
  beta_reduce
  ring

/-- The separated real dual kernel after the full rectangle integration. -/
def dualSeparatedKernel (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (W : G n → ℂ) (V : H → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Q t × Chart) : ℂ :=
  let z := p.2.1.1.1.1
  let C := retainedTail k q p.2.1 p.2.2.2
  let Ξ := leadingRestriction k (q + 1) k C T.leading
  let x := (rectangleRows t q).symm p.2.2.1
  detCharacter c.inverse.character.toMonoidHom (weylLong m ℝ) * retainedCoefficient t q a c T C *
    weightedDual (rankLT t q) (ρ C⁻¹ W) (ρ z V) f₁ (p.1, x) *
    realAdjacentMatrixWeight c.inverse.character.toMonoidHom (realRectangularSchwartzFourier a Ξ) 0
      (ι₁ z) * f₂ (δ (ι₁ z))

private theorem integrate_full_rectangle (a : ℝˣ) (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ))
    (T : GodementColumnFactors k q) (hT : ∀ B, Fs B = T.squareEval k q B)
    (W : G n → ℂ) (V : H → ℂ) (hW : HasLeftCharacter (-a) W) (hV : HasLeftCharacter a V)
    (f₁ f₂ : ℝ → ℂ) (u : Q t) (p : Chart) :
    let z := ι₁ p.1.1.1.1
    let Xμ := rectangularMeasure (μ a) (n - k) k
    (∫ x : X, dualChartWeightedKernel t q a c Fs T (ArchimedeanLocal.dualFunction n W)
      (ArchimedeanLocal.dualFunction k V) f₁ f₂ (rightTranslate (N k) z u, x, p) ∂Xμ) =
      dualSeparatedKernel t q a c T W V f₁ f₂ (u, p) := by
  intro z Xμ
  let Wd := ArchimedeanLocal.dualFunction n W
  let Vd := ArchimedeanLocal.dualFunction k V
  let C := retainedTail k q p.1 p.2.2
  let e := rectangleRows t m
  let η := rectangularMeasure (μ a) m k
  let h := p.1.1.1.1
  have hz : 0 < δ z := abs_pos.mpr z.det_ne_zero
  have hWd : HasLeftCharacter a Wd := by
    simpa only [neg_neg] using hW.dual
  have hVd : HasLeftCharacter (-a) Vd := hV.dual
  induction u using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk]
    change (∫ x : X, dualChartWeightedKernel t q a c Fs T Wd Vd f₁ f₂
      (Quotient.mk _ (g * z), x, p) ∂Xμ) = _
    have hkernel (x : X) := dualChartWeightedKernel_mk t q a c Fs T Wd Vd hWd hVd f₁ f₂ (g * z) x p
    dsimp only at hkernel
    simp_rw [hkernel]
    have hcancel : δ (g * z) * (δ z)⁻¹ = δ g := by
      rw [detAbs_mul, mul_assoc, mul_inv_cancel₀ hz.ne', mul_one]
    change (∫ x : X, unitDualKernel k q a c Fs T Wd (g * z) (e x) p * Vd (g * z) *
      P (g * z) (0 - gap) * f₁ (δ (g * z) * (δ z)⁻¹) * f₂ (δ z) ∂Xμ) = _
    rw [hcancel]
    simp_rw [integral_mul_const]
    have hMP : MeasurePreserving e Xμ η := measurePreserving_rectangleRows t m (μ a)
    have hInt : (∫ x : X, unitDualKernel k q a c Fs T Wd (g * z) (e x) p ∂Xμ) =
        ∫ x : M m k, unitDualKernel k q a c Fs T Wd (g * z) x p ∂η :=
      hMP.integral_comp' (fun x => unitDualKernel k q a c Fs T Wd (g * z) x p)
    rw [hInt, mul_right_comm _ (Vd (g * z)) (P (g * z) (0 - gap)), mul_comm _ (P (g * z) (0 - gap))]
    have hsep := unitDualKernel_separate t q a c Fs T hT Wd g p.1 p.2.2 p.2.1 0
    dsimp only at hsep
    change P (g * z) (0 - gap) * (∫ x : M m k, unitDualKernel k q a c Fs T Wd (g * z) x p ∂η) = _
      at hsep
    rw [hsep]
    unfold dualSeparatedKernel weightedDual
    dsimp only [Prod.fst, Prod.snd]
    have hVt : HasLeftCharacter (-(-a)) (ρ h V) := by simpa only [neg_neg] using left_translate hV h
    rw [dualKernel_mk (rankLT t q) (left_translate hW C⁻¹) hVt, quotientDetAbs_mk]
    have hT' : ρ (ArchimedeanLocal.unfoldingWeyl (rankLT t q)) (ArchimedeanLocal.dualFunction n (ρ C⁻¹ W))
        (ArchimedeanLocal.rectangularPoint (rankLT t q) g ((rectangleRows t q).symm p.2.1)) =
        Wd (RealGapDualArguments.lowerPoint k q g p.2.1 * RealGapWeylRestriction.tailWeyl k m *
          (inverseTranspose n ℝ C)⁻¹) := by
      have h₀ := translated_dualPoint t q W C g ((rectangleRows t q).symm p.2.1)
      rw [MeasurableEquiv.apply_symm_apply] at h₀
      exact h₀
    rw [hT', show r - t = q + 1 by omega, ← detPower_eq_exp_logDet]
    have hVtranslate : ArchimedeanLocal.dualFunction k (ρ h V) g = Vd (g * z) := by
      unfold Vd ArchimedeanLocal.dualFunction ArchimedeanLocal.translateFunction
      simp only [map_mul, mul_assoc, z, h, Langlands.GeneralLinear.inverseTranspose_involutive]
    rw [hVtranslate]
    dsimp only [z, C, Wd, h]
    ring

/-- The real dual Haar and rectangle integration can be replaced by the separated dual kernel. -/
def RealGapDualSeparationStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H) (κ : Measure (KU n)),
    η₁.IsHaarMeasure → κ.IsHaarMeasure →
    ∀ (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q),
      (∀ B, Fs B = T.squareEval k q B) →
    ∀ (W : G n → ℂ) (V : H → ℂ), HasLeftCharacter (-a) W → HasLeftCharacter a V →
    ∀ (f₁ f₂ : ℝ → ℂ),
    let A := D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a η₁ κ))
    let B := D.measure.prod (dualChartMeasure t q a η₁ κ)
    let F := dualChartWeightedKernel t q a c Fs T (ArchimedeanLocal.dualFunction n W)
      (ArchimedeanLocal.dualFunction k V) f₁ f₂
    let Fs := dualSeparatedKernel t q a c T W V f₁ f₂
    Integrable F A → Integrable Fs B ∧ (∫ p, F p ∂A) = ∫ p, Fs p ∂B

set_option maxHeartbeats 1200000 in
theorem realGapDualSeparation : RealGapDualSeparationStatement t q := by
  intro D a η₁ κ hη₁ hκ c Fs T hT W V hW hV f₁ f₂
  dsimp only
  intro hF
  let A := D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a η₁ κ))
  let ξ := rectangularMeasure (μ a) (n - k) k
  let η := dualChartMeasure t q a η₁ κ
  let F := dualChartWeightedKernel t q a c Fs T (ArchimedeanLocal.dualFunction n W)
    (ArchimedeanLocal.dualFunction k V) f₁ f₂
  let Fsep := dualSeparatedKernel t q a c T W V f₁ f₂
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : (μ a).measure.IsAddHaarMeasure := (μ a).isAddHaar
  let : ξ.IsAddHaarMeasure := rectangularMeasure_isAddHaar (μ a) _ _
  let : SigmaFinite ξ := inferInstance
  let : SigmaFinite η := sigmaFinite_dualChartMeasure t q a η₁ κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let lead (p : X × Chart) := ι₁ p.2.1.1.1.1
  have hl : Measurable lead := (inverseTransposeContinuous k ℝ).continuous.measurable.comp (by fun_prop)
  let shift := quotientShift (N k) lead hl
  have hshift : MeasurePreserving shift A A :=
    measurePreserving_quotientShift (N k) D.measure (ξ.prod η) D.compatible.right_invariant lead hl
  let e := interchangeMiddle (A := Q t) (B := X) (C := Chart)
  have he : MeasurePreserving e ((D.measure.prod η).prod ξ) A :=
    measurePreserving_interchangeMiddle D.measure ξ η
  let J := F ∘ shift ∘ e
  have hJ : Integrable J ((D.measure.prod η).prod ξ) :=
    he.integrable_comp_of_integrable (hshift.integrable_comp_of_integrable hF)
  have hpt (p : Q t × Chart) : (∫ x : X, J (p, x) ∂ξ) = Fsep p :=
    integrate_full_rectangle t q a c Fs T hT W V hW hV f₁ f₂ p.1 p.2
  change Integrable Fsep (D.measure.prod η) ∧ (∫ p, F p ∂A) = ∫ p, Fsep p ∂D.measure.prod η
  refine ⟨hJ.integral_prod_left.congr (ae_of_all _ hpt), ?_⟩
  calc
    _ = ∫ p, (F ∘ shift) p ∂A := (hshift.integral_comp shift.measurableEmbedding F).symm
    _ = ∫ p, J p ∂(D.measure.prod η).prod ξ :=
      (he.integral_comp e.measurableEmbedding (F ∘ shift)).symm
    _ = ∫ p, Fsep p ∂D.measure.prod η :=
      (integral_prod J hJ).trans (integral_congr_ae (ae_of_all _ hpt))

end Langlands.Global.RankinSelbergGlobal.RealGapDualSeparation
