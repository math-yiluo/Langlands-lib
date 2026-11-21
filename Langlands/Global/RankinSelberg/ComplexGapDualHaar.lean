import Langlands.Global.RankinSelberg.ComplexGapPartialFactors
import Langlands.Global.RankinSelberg.ComplexGapExactRestriction

/-! # Joint convergence on the full dual chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapDualHaar

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant inverseTranspose rankInclusion)
open Langlands.GodementJacquet (complexSelfDualMeasure_neg_scale)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar det_rankInclusion)
open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure complexNormalizedAbs)
open ArchimedeanMellinPair (RapidDecay)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapDualChart (dualChart dualRetained measurable_dualChart lowerShear determinant_lowerShear
  normalizedAbs_retainedTail complexGapDualChart)
open ComplexGapLeadingFourier (rectTransform)
open ComplexGapNormalizedRestriction (unitDualKernel)
open ComplexGapNormalizedWeighted (padGL_eq_rankInclusion)
open ComplexGapOrdinaryWeighted (coupledHaarKernel coupledHaarKernel_eq complexGapCoupledHaarPowerBounds)
open ComplexGapPartialFactors (complexGapPartialFactors)
open ComplexGapRankCoordinates (rankLT rectangleRows rectangularPoint_eq_consecutive)
open ComplexGapSplitFourier (fourierFactors complexGapSplitFourier)
open ComplexGapTriangularChart (Outer outerMeasure)
open ComplexGapUnitDeterminant (unitOuterMeasure)
open ComplexGapWeylRestriction (normalizedAbs_det_tailWeyl)
open ComplexGodementLowerRectangle (lowerRectangle rectangularPoint_eq_pad_lowerRectangle)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexUnequalMellinReduction (quotientDetAbs)

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

/-- Multiplicativity of the normalized complex determinant. -/
theorem detAbs_mul {n : ℕ} (A B : G n) : δ (A * B) = δ A * δ B := by
  simp only [Units.val_mul, Matrix.det_mul, complexNormalizedAbs, norm_mul, mul_pow]

/-- Inverse transpose inverts the normalized complex determinant. -/
theorem detAbs_inverseTranspose {n : ℕ} (g : G n) : δ (inverseTranspose n ℂ g) = (δ g)⁻¹ := by
  have hg : 0 < δ g := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  have hι : δ (inverseTranspose n ℂ g) = δ g⁻¹ := by
    simp only [Langlands.GeneralLinear.inverseTranspose_coe, Matrix.det_transpose]
  rw [hι]
  apply mul_left_cancel₀ hg.ne'
  rw [← detAbs_mul, mul_inv_cancel, mul_inv_cancel₀ hg.ne']
  simp [complexNormalizedAbs]

variable (t q : ℕ)
local notation "k" => t + 1
local notation "m" => q + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "X" => M (n - k) k
local notation "U" => M q k
local notation "Chart" => Outer k q × (U × N m)
local notation "Joint" => Q t × (X × Chart)
local notation "ι₁" => inverseTranspose k ℂ
local notation "Test" => 𝓢(M n (n + 1), ℂ)
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
  have hb : δ (lowerShear k q (-ComplexGapDualChart.extendLower k q p.2.1)) = 1 := by
    change complexNormalizedAbs ((determinant (lowerShear k q
      (-ComplexGapDualChart.extendLower k q p.2.1)) : ℂˣ) : ℂ) = 1
    rw [determinant_lowerShear]
    simp [complexNormalizedAbs]
  simp only [dualChart, dualRetained, detAbs_mul, detAbs_inverseTranspose,
    normalizedAbs_retainedTail k q (Nat.succ_pos t), inv_one,
    normalizedAbs_det_tailWeyl, hb, det_rankInclusion, one_mul]

/-- The joint measure for the full dual chart before integration in the complementary rectangle. -/
def dualChartMeasure (a : ℂˣ) (κ : Measure (KU n)) : Measure Chart :=
  (unitOuterMeasure k q (μ a) κ).prod ((rectangularMeasure (μ a) q k).prod (entryHaar (μ a) m))

/-- The dual chart measure is sigma finite for compact Haar measure on the unitary group. -/
theorem sigmaFinite_dualChartMeasure (a : ℂˣ) (κ : Measure (KU n)) [κ.IsHaarMeasure] :
    SigmaFinite (dualChartMeasure t q a κ) := by
  let : CompactSpace (KU n) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : (μ a).measure.IsAddHaarMeasure := (μ a).isAddHaar
  let : SigmaFinite (μ a).measure := inferInstance
  let : SigmaFinite (entryHaar (μ a) m) := entryHaar_sigmaFinite (μ a) m
  let : SigmaFinite (outerMeasure k q (μ a) κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite (unitOuterMeasure k q (μ a) κ) := SigmaFinite.withDensity _
  unfold dualChartMeasure
  infer_instance

/-- The full normalized dual integrand with rapid profiles on the two separated determinants. -/
def dualChartWeightedKernel (a : ℂˣ) (d : ComplexCharacterData) (Φ : Test)
    (Wd : G n → ℂ) (Vd : G k → ℂ) (s : ℂ) (f₁ f₂ : ℝ → ℂ) (p : Joint) : ℂ :=
  let z := ι₁ p.2.2.1.1.1.1
  unitDualKernel k q a d Φ Wd p.1.out s (rectangleRows t m p.2.1) p.2.2 *
    Vd p.1.out * P p.1.out (0 - gap) * f₁ (quotientDetAbs p.1 * (δ z)⁻¹) * f₂ (δ z)

/-- Pulling the ambient coupled kernel back along the dual Haar chart gives the indicated profiles. -/
theorem dualChartWeightedKernel_eq (a : ℂˣ) (d : ComplexCharacterData) (Φ : Test)
    (Wd : G n → ℂ) (Vd : G k → ℂ) (s : ℂ) (f₁ f₂ : ℝ → ℂ) (p : Joint) :
    coupledHaarKernel (rankLT t q) (μ a) d.inv (-a) (rectTransform a Φ) Wd Vd (-s) f₁ f₂
      (p.1, p.2.1, dualChart k q p.2.2) = dualChartWeightedKernel t q a d Φ Wd Vd s f₁ f₂ p := by
  have hpad (g : G k) : padGL (Nat.succ_le_succ (rankLT t q).le) g = rankInclusion m g :=
    padGL_eq_rankInclusion k q g
  rw [coupledHaarKernel_eq, detAbs_dualChart, lowerRectangle_eq_lowerShear, hpad]
  unfold dualChartWeightedKernel
  rw [show r - t = q + 1 by omega]
  rfl

/-- Before any complementary rectangle integration, the exact full dual kernel with two rapid
profiles is integrable over the smaller quotient, the full rectangle, and the dual Haar chart. -/
def ComplexGapDualHaarStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU n)),
    κ.IsHaarMeasure → κ.IsInvInvariant →
    ∀ (ds es : List ComplexCharacterData) (Wd : complexWhittakerModel r ds a)
      (Vd : complexWhittakerModel t es (-a)) (d : ComplexCharacterData) (Φ : Test)
      (T : GodementColumnFactors k q), (∀ x, Φ x = T.eval k q x) →
    ∀ (s : ℂ) (f₁ f₂ : ℝ → ℂ), Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
    Integrable (dualChartWeightedKernel t q a d Φ Wd.val Vd.val s f₁ f₂)
      (D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a κ)))

set_option maxHeartbeats 800000 in
/-- The two radial profiles on the dual chart only need bounds by sufficiently large powers. -/
theorem complexGapDualHaarPowerBounds (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU n))
    (hκ : κ.IsHaarMeasure) (hκinv : κ.IsInvInvariant)
    (ds es : List ComplexCharacterData) (Wd : complexWhittakerModel r ds a)
    (Vd : complexWhittakerModel t es (-a)) (d : ComplexCharacterData) (Φ : Test)
    (T : GodementColumnFactors k q) (hT : ∀ x, Φ x = T.eval k q x) (s : ℂ) :
    ∃ α₀ γ₀ : ℝ, ∀ (f₁ f₂ : ℝ → ℂ) (α γ C₁ C₂ : ℝ),
      α₀ ≤ α → γ₀ ≤ γ → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ α) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ γ) →
      Integrable (dualChartWeightedKernel t q a d Φ Wd.val Vd.val s f₁ f₂)
        (D.measure.prod ((rectangularMeasure (μ a) (n - k) k).prod (dualChartMeasure t q a κ))) := by
  let Ψ := rectTransform a Φ
  let T' := fourierFactors k q a T
  have hΨ : ∀ x, Ψ x = T'.eval k q x := complexGapSplitFourier k q a Φ T hT
  have hSplit := complexGapPartialFactors t q (-a) Ψ T' hΨ
  rw [complexSelfDualMeasure_neg_scale] at hSplit
  let W' : complexWhittakerModel r ds (-(-a)) := ⟨Wd.val, by simpa only [neg_neg] using Wd.2⟩
  obtain ⟨α₀, γ₀, hI⟩ := complexGapCoupledHaarPowerBounds r t (rankLT t q) D (μ a) (μ a) κ hκ hκinv
    ds es (-a) W' Vd d.inv Ψ _ _ _ hSplit (-s)
  refine ⟨α₀, γ₀, ?_⟩
  intro f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  let F := coupledHaarKernel (rankLT t q) (μ a) d.inv (-a) Ψ Wd.val Vd.val (-s) f₁ f₂
  let η := rectangularMeasure (μ a) (n - k) k
  let ρ := dualChartMeasure t q a κ
  let e : Joint → Q t × (X × G n) := Prod.map id (Prod.map id (dualChart k q))
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace (KU n) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : SecondCountableTopology (KU n) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : (μ a).measure.IsAddHaarMeasure := (μ a).isAddHaar
  let : SigmaFinite (μ a).measure := inferInstance
  let : SigmaFinite (entryHaar (μ a) m) := entryHaar_sigmaFinite (μ a) m
  let : SigmaFinite (outerMeasure k q (μ a) κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite (unitOuterMeasure k q (μ a) κ) := SigmaFinite.withDensity _
  let : SigmaFinite ρ := by unfold ρ dualChartMeasure; infer_instance
  let : η.IsAddHaarMeasure := rectangularMeasure_isAddHaar (μ a) _ _
  let : SigmaFinite η := inferInstance
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : LocallyCompactSpace (G k) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) k).locallyCompactSpace
  let : SecondCountableTopology (G k) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) k).isInducing.secondCountableTopology
  let : SigmaCompactSpace (Q t) := by
    let : SigmaCompactSpace (G k) := sigmaCompactSpace_of_locallyCompact_secondCountable
    have hQ := leftQuotient_isOpenQuotientMap (N k)
    rw [← isSigmaCompact_univ_iff, ← Set.range_eq_univ.mpr hQ.surjective]
    exact isSigmaCompact_range hQ.continuous
  have hF : Integrable F (D.measure.prod (η.prod (complexGeneralLinearHaar n))) :=
    hI f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  obtain ⟨c, hc, _, hd⟩ := complexGapDualChart k q (Nat.succ_pos t) (μ a) κ hκ hκinv
  change complexGeneralLinearHaar n = c • ρ.map (dualChart k q) at hd
  rw [hd, Measure.prod_smul_right, Measure.prod_smul_right] at hF
  have hF' := (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hF
  have hChart : MeasurePreserving (dualChart k q) ρ (ρ.map (dualChart k q)) := ⟨measurable_dualChart k q, rfl⟩
  have he : MeasurePreserving e (D.measure.prod (η.prod ρ))
      (D.measure.prod (η.prod (ρ.map (dualChart k q)))) :=
    (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hChart)
  have heq : F ∘ e = dualChartWeightedKernel t q a d Φ Wd.val Vd.val s f₁ f₂ :=
    funext (dualChartWeightedKernel_eq t q a d Φ Wd.val Vd.val s f₁ f₂)
  rw [← heq]
  exact (he.integrable_comp hF'.aestronglyMeasurable).mpr hF'

theorem complexGapDualHaar : ComplexGapDualHaarStatement t q := by
  intro D a κ hκ hκinv ds es Wd Vd d Φ T hT s f₁ f₂ hm₁ hm₂ hf₁ hf₂
  obtain ⟨α, γ, hI⟩ := complexGapDualHaarPowerBounds t q D a κ hκ hκinv ds es Wd Vd d Φ T hT s
  obtain ⟨C₁, h₁⟩ := hf₁ α
  obtain ⟨C₂, h₂⟩ := hf₂ γ
  exact hI f₁ f₂ α γ C₁ C₂ le_rfl le_rfl hm₁ hm₂ h₁ h₂

end Langlands.Global.RankinSelbergGlobal.ComplexGapDualHaar
