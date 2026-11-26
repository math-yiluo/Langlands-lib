import Langlands.Global.RankinSelberg.RealGapPartialFactors
import Langlands.Global.RankinSelberg.RealGapExactRestriction

/-! # Joint convergence on the full real dual chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapDualHaar

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant inverseTranspose rankInclusion)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar det_rankInclusion)
open ArchimedeanLocal (RealQuotientMeasureData realSelfDualMeasure realNormalizedAbs realFourierTransform)
open ArchimedeanMellinPair (RapidDecay)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapDualChart (dualChart dualRetained measurable_dualChart lowerShear determinant_lowerShear
  normalizedAbs_retainedTail realGapDualChart extendLower)
open RealGapNormalizedRestriction (unitDualKernel)
open RealGapNormalizedWeighted (padGL_eq_rankInclusion)
open RealGapOrdinaryWeighted (HasSplitPartialTest coupledHaarKernel coupledHaarKernel_eq
  realGapCoupledHaarPowerBounds)
open RealGapPartialFactors (realGapPartialFactors)
open RealGapRankCoordinates (rankLT rectangleRows rectangularPoint_eq_consecutive)
open RealGapSplitFourier (fourierFactors realGapSplitFourier)
open RealGapTriangularChart (Outer outerMeasure)
open RealGapUnitDeterminant (unitOuterMeasure)
open RealGapWeylRestriction (abs_det_tailWeyl)
open RealGodementLowerRectangle (lowerRectangle rectangularPoint_eq_pad_lowerRectangle)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealUnequalMellinReduction (quotientDetAbs)
open RealGodement (realRectangularSchwartzFourier realRowSchwartzFourier realRowSchwartzFourier_apply
  realRowSchwartzFourier_neg_comp)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "μ" => realSelfDualMeasure

local instance gapDualHaarGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapDualHaarGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapDualHaarGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapDualHaarGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapDualHaarUMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance gapDualHaarUBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩
local instance gapDualHaarQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapDualHaarQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

/-- Multiplicativity of the absolute determinant. -/
theorem detAbs_mul {n : ℕ} (A B : G n) : δ (A * B) = δ A * δ B := by
  simp only [Units.val_mul, Matrix.det_mul, realNormalizedAbs, abs_mul]

/-- Inverse transpose inverts the absolute determinant. -/
theorem detAbs_inverseTranspose {n : ℕ} (g : G n) : δ (inverseTranspose n ℝ g) = (δ g)⁻¹ := by
  have hg : 0 < δ g := abs_pos.mpr g.det_ne_zero
  have hι : δ (inverseTranspose n ℝ g) = δ g⁻¹ := by
    simp only [Langlands.GeneralLinear.inverseTranspose_coe, Matrix.det_transpose]
  rw [hι]
  apply mul_left_cancel₀ hg.ne'
  rw [← detAbs_mul, mul_inv_cancel, mul_inv_cancel₀ hg.ne']
  simp [realNormalizedAbs]

variable (t q : ℕ)
local notation "k" => t + 1
local notation "m" => q + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "X" => M (n - k) k
local notation "U" => M q k
local notation "Chart" => Outer k q × (U × N m)
local notation "Joint" => Q t × (X × Chart)
local notation "ι₁" => inverseTranspose k ℝ
local notation "Sq" => M n n
local notation "gap" => (((q + 1 : ℕ) : ℂ) / 2)

/-- The input rectangle insertion becomes the lower shear after reindexing its rows. -/
theorem lowerRectangle_eq_lowerShear (x : X) :
    lowerRectangle (rankLT t q) x = lowerShear k q (rectangleRows t m x) := by
  let L := lowerRectangle (rankLT t q) x
  let R := lowerShear k q (rectangleRows t m x)
  have he : padGL (Nat.le_succ n) L = padGL (Nat.le_succ n) R := by
    have h₁ := rectangularPoint_eq_pad_lowerRectangle (rankLT t q) (1 : G k) x
    have h₂ := rectangularPoint_eq_consecutive t q (1 : G k) x
    simp only [map_one, one_mul] at h₁ h₂
    exact h₁.symm.trans h₂
  apply Units.ext
  funext i j
  have hij := congrArg (fun g : G (n + 1) => g.val i.castSucc j.castSucc) he
  simpa only [Unfolding.padGL_apply, Fin.val_castSucc, dite_eq_left i.isLt, dite_eq_left j.isLt] using hij

/-- The determinant of the dual chart is the determinant of its inverse-transpose leading factor. -/
theorem detAbs_dualChart (p : Chart) : δ (dualChart k q p) = δ (ι₁ p.1.1.1.1) := by
  have hb : δ (lowerShear k q (-extendLower k q p.2.1)) = 1 := by
    change realNormalizedAbs ((determinant (lowerShear k q (-extendLower k q p.2.1)) : ℝˣ) : ℝ) = 1
    rw [determinant_lowerShear]
    simp [realNormalizedAbs]
  have hw : δ (RealGapWeylRestriction.tailWeyl k m) = 1 := abs_det_tailWeyl k m
  have hA : δ (rankInclusion (q + 1) (ι₁ p.1.1.1.1)) = δ (ι₁ p.1.1.1.1) := by
    change realNormalizedAbs (rankInclusion (q + 1) (ι₁ p.1.1.1.1)).val.det = _
    rw [det_rankInclusion]
  simp only [dualChart, dualRetained, detAbs_mul, detAbs_inverseTranspose,
    normalizedAbs_retainedTail k q (Nat.succ_pos t), inv_one, hw, hb, hA, one_mul]

/-- The joint measure for the full dual chart before integration in the complementary rectangle. -/
def dualChartMeasure (a : ℝˣ) (η₁ : Measure (G k)) (κ : Measure (KU n)) : Measure Chart :=
  (unitOuterMeasure k q (μ a) η₁ κ).prod ((rectangularMeasure (μ a) q k).prod (entryHaar (μ a) m))

/-- The dual chart measure is sigma finite for Haar measures. -/
theorem sigmaFinite_dualChartMeasure (a : ℝˣ) (η₁ : Measure (G k)) (κ : Measure (KU n))
    [η₁.IsHaarMeasure] [κ.IsHaarMeasure] : SigmaFinite (dualChartMeasure t q a η₁ κ) := by
  let : (μ a).measure.IsAddHaarMeasure := (μ a).isAddHaar
  let : SigmaFinite (μ a).measure := inferInstance
  let : SigmaFinite (entryHaar (μ a) m) := entryHaar_sigmaFinite (μ a) m
  let : SecondCountableTopology (KU n) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SigmaFinite (outerMeasure k q (μ a) η₁ κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite (unitOuterMeasure k q (μ a) η₁ κ) := SigmaFinite.withDensity _
  unfold dualChartMeasure
  infer_instance

/-- The full normalized dual integrand with rapid profiles on the two separated determinants. -/
def dualChartWeightedKernel (a : ℝˣ) (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ))
    (T : GodementColumnFactors k q) (Wd : G n → ℂ) (Vd : G k → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Joint) : ℂ :=
  let z := ι₁ p.2.2.1.1.1.1
  unitDualKernel k q a c Fs T Wd p.1.out (rectangleRows t m p.2.1) p.2.2 *
    Vd p.1.out * P p.1.out (0 - gap) * f₁ (quotientDetAbs p.1 * (δ z)⁻¹) * f₂ (δ z)

/-- Pulling the ambient coupled kernel back along the dual Haar chart gives the indicated profiles. -/
theorem dualChartWeightedKernel_eq (a : ℝˣ) (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ))
    (T : GodementColumnFactors k q) (Wd : G n → ℂ) (Vd : G k → ℂ) (f₁ f₂ : ℝ → ℂ) (p : Joint) :
    coupledHaarKernel (rankLT t q) c.inverse (-a) (realRectangularSchwartzFourier a Fs)
        (realRowSchwartzFourier n a (T.tail (Fin.last (q + 1)))) Wd Vd f₁ f₂
        (p.1, p.2.1, dualChart k q p.2.2) =
      dualChartWeightedKernel t q a c Fs T Wd Vd f₁ f₂ p := by
  have hpad (g : G k) : padGL (Nat.succ_le_succ (rankLT t q).le) g = rankInclusion m g :=
    padGL_eq_rankInclusion k q g
  rw [coupledHaarKernel_eq, detAbs_dualChart, lowerRectangle_eq_lowerShear, hpad]
  unfold dualChartWeightedKernel
  rw [show r - t = q + 1 by omega]
  rfl

/-- Before any complementary rectangle integration, the exact full dual kernel with two rapid
profiles is integrable over the smaller quotient, the full rectangle, and the dual Haar chart. -/
def RealGapDualHaarStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure (G k)) (κ : Measure (KU n)),
    η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∀ (ds es : List RealBlock) (Wd : G n → ℂ) (Vd : G k → ℂ),
      Wd ∈ realUniformWhittakerModel r ds a → Vd ∈ realUniformWhittakerModel t es (-a) →
    ∀ (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q),
      (∀ B, Fs B = T.squareEval k q B) →
    ∀ (f₁ f₂ : ℝ → ℂ), Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
    Integrable (dualChartWeightedKernel t q a c Fs T Wd Vd f₁ f₂)
      (D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a η₁ κ)))

set_option maxHeartbeats 1000000 in
/-- The two radial profiles on the dual chart only need bounds by sufficiently large powers. -/
theorem realGapDualHaarPowerBounds (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure (G k))
    (κ : Measure (KU n)) [η₁.IsHaarMeasure] [κ.IsHaarMeasure] (hκinv : κ.IsInvInvariant)
    (ds es : List RealBlock) (Wd : G n → ℂ) (Vd : G k → ℂ)
    (hWd : Wd ∈ realUniformWhittakerModel r ds a) (hVd : Vd ∈ realUniformWhittakerModel t es (-a))
    (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q)
    (hT : ∀ B, Fs B = T.squareEval k q B) :
    ∃ α₀ γ₀ : ℝ, ∀ (f₁ f₂ : ℝ → ℂ) (α γ C₁ C₂ : ℝ),
      α₀ ≤ α → γ₀ ≤ γ → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ α) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ γ) →
      Integrable (dualChartWeightedKernel t q a c Fs T Wd Vd f₁ f₂)
        (D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a η₁ κ))) := by
  let Fh := realRectangularSchwartzFourier a Fs
  let fh := realRowSchwartzFourier n a (T.tail (Fin.last (q + 1)))
  let T' := fourierFactors k q a T
  have hP := realGapPartialFactors t q (-a) T'
  have hSplit : HasSplitPartialTest (rankLT t q) (-a) Fh fh T'.leading
      (RealGapPartialFactors.columnProduct n (n - k) (fun j => T'.tail
        ((finCongr (by omega : t + 1 + q + 1 - (t + 1) = q + 1)) j).castSucc))
      (T.tail (Fin.last (q + 1))) := by
    refine ⟨fun C => ?_, fun v => ?_⟩
    · rw [← hP.1 C]
      exact realGapSplitFourier k q a Fs T hT C.val
    · rw [← funext (realRowSchwartzFourier_apply n (-a) fh)]
      exact congrArg (fun f : 𝓢(Fin n → ℝ, ℂ) => f v)
        (realRowSchwartzFourier_neg_comp n a (T.tail (Fin.last (q + 1))))
  have hWd' : Wd ∈ realUniformWhittakerModel r ds (-(-a)) := by simpa only [neg_neg] using hWd
  let Haar : Measure (G n) := Measure.haar
  obtain ⟨α₀, γ₀, hI⟩ := realGapCoupledHaarPowerBounds r t (rankLT t q) D (μ a) Haar κ hκinv
    ds es (-a) Wd Vd hWd' hVd c.inverse Fh fh _ _ _ hSplit
  refine ⟨α₀, γ₀, ?_⟩
  intro f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  let K := coupledHaarKernel (rankLT t q) c.inverse (-a) Fh fh Wd Vd f₁ f₂
  let η := rectangularMeasure (μ a) (n - k) k
  let ρ := dualChartMeasure t q a η₁ κ
  let e : Joint → Q t × (X × G n) := Prod.map id (Prod.map id (dualChart k q))
  let : SecondCountableTopology (KU n) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SigmaFinite ρ := sigmaFinite_dualChartMeasure t q a η₁ κ
  let : (μ a).measure.IsAddHaarMeasure := (μ a).isAddHaar
  let : η.IsAddHaarMeasure := rectangularMeasure_isAddHaar (μ a) _ _
  let : SigmaFinite η := inferInstance
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  have hF : Integrable K (D.measure.prod (η.prod Haar)) :=
    hI f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  obtain ⟨cH, hc, _, hd⟩ := realGapDualChart k q (Nat.succ_pos t) (μ a) Haar η₁ κ inferInstance
    inferInstance inferInstance hκinv
  change Haar = cH • ρ.map (dualChart k q) at hd
  rw [hd, Measure.prod_smul_right, Measure.prod_smul_right] at hF
  have hF' := (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hF
  have hChart : MeasurePreserving (dualChart k q) ρ (ρ.map (dualChart k q)) :=
    ⟨measurable_dualChart k q, rfl⟩
  have he : MeasurePreserving e (D.measure.prod (η.prod ρ))
      (D.measure.prod (η.prod (ρ.map (dualChart k q)))) :=
    (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hChart)
  have heq : K ∘ e = dualChartWeightedKernel t q a c Fs T Wd Vd f₁ f₂ :=
    funext (dualChartWeightedKernel_eq t q a c Fs T Wd Vd f₁ f₂)
  rw [← heq]
  exact (he.integrable_comp hF'.aestronglyMeasurable).mpr hF'

theorem realGapDualHaar : RealGapDualHaarStatement t q := by
  intro D a η₁ κ hη₁ hκ hκinv ds es Wd Vd hWd hVd c Fs T hT f₁ f₂ hm₁ hm₂ hf₁ hf₂
  obtain ⟨α, γ, hI⟩ := realGapDualHaarPowerBounds t q D a η₁ κ hκinv ds es Wd Vd hWd hVd c Fs T hT
  obtain ⟨C₁, h₁⟩ := hf₁ α
  obtain ⟨C₂, h₂⟩ := hf₂ γ
  exact hI f₁ f₂ α γ C₁ C₂ le_rfl le_rfl hm₁ hm₂ h₁ h₂

end Langlands.Global.RankinSelbergGlobal.RealGapDualHaar
