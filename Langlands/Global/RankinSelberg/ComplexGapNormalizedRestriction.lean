import Langlands.Global.RankinSelberg.ComplexGapMatchedTests

/-! # Ordinary and dual Godement restriction with one Haar constant -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapNormalizedRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (rankInclusion determinant weylLong)
open Langlands.GodementJacquet (complexSelfDualMeasure_neg_scale)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (rectangularMeasure det_rankInclusion)
open ArchimedeanLocal (complexSelfDualMeasure complexNormalizedAbs)
open ComplexGapAlternateRestriction (GodementColumnFactors restrictionWeight paddedRestrictionKernel_split)
open ComplexGapDualChart (retainedTail dualChart measurable_dualChart lowerShear determinant_lowerShear complexGapDualChart)
open ComplexGapLeadingFourier (rectTransform)
open ComplexGapMatchedTests (dualFiber)
open ComplexGapTailExchange (alternateBlockTailKernel ordinaryBlockTailKernel complexGapTailExchange)
open ComplexGapTriangularChart (Outer outerMeasure)
open ComplexGapUnitDeterminant (unitRetained unitDeterminantChart unitOuterMeasure normalizedAbs_unitRetained
  continuous_unitDeterminantChart)
open ComplexGapWeylRestriction (tailWeyl reverseTail continuedValue_mul_right rightTest_tailWeyl_eval
  normalizedAbs_det_tailWeyl determinant_tailWeyl)
open ComplexGodement (characterWeight normPower)
open ComplexGodementAddedCharacter (continuedValue rightTest)
open ComplexGodementPaddedRestriction (paddedRestrictionKernel complexGodementPaddedRestriction normPower_determinant)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

local notation "GLc" => fun n => Langlands.GeneralLinear n ℂ
local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (GLc n) := borel _
local instance gapGLBorel (n : ℕ) : BorelSpace (GLc n) := ⟨rfl⟩

open scoped Matrix.Norms.Operator in
private theorem gapGLSecondCountable (n : ℕ) : SecondCountableTopology (GLc n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable (k q : ℕ)
local notation "G" => GLc (k + q + 1)
local notation "H" => GLc k
local notation "A" => rankInclusion (R := ℂ) (n := k) (q + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "Remainder" => Matrix (Fin k) (Fin q) ℂ × N
local notation "DualRemainder" => Matrix (Fin q) (Fin k) ℂ × N
local notation "FullLower" => Matrix (Fin (q + 1)) (Fin k) ℂ
local notation "I" => Fin (k + q + 1)
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℂ
local notation "Compact" => unitaryCompact ℂ (k + q + 1)
local notation "pad" => padGL (Nat.le_succ (k + q + 1))
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

local instance gapNMeasurable : MeasurableSpace N := borel _
local instance gapNBorel : BorelSpace N := ⟨rfl⟩

/-- The alternate ordinary split kernel on the determinant-normalized chart. -/
def unitOrdinaryKernel (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (W : G → ℂ) (g : H) (s : ℂ) (p : Outer k q) (Z : N) : ℂ :=
  alternateBlockTailKernel k q a ((reverseTail k q T).partial k q a) W (restrictionWeight k q d s)
    g p.1.1.1 (unitRetained k q p) Z

/-- The full dual kernel in the dual chart, with the outer complementary rectangle fixed. -/
def unitDualKernel (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (Wd : G → ℂ)
    (g : H) (s : ℂ) (X : FullLower) (p : Outer k q × DualRemainder) : ℂ :=
  dualFiber k q a d Φ Wd g p.1.1.1.1 (retainedTail k q p.1 p.2.2) p.2.1 s X

private theorem pullback_integral {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → ℂ} {chart : Y → X}
    (hm : Measurable chart) {c : ℝ≥0} (hc : 0 < c) (hν : μ = c • ν.map chart) (hf : Integrable f μ) :
    Integrable (f ∘ chart) ν ∧ (∫ x, f x ∂μ) = (c : ℂ) * ∫ p, f (chart p) ∂ν := by
  have hMap : Integrable f (ν.map chart) := by
    rw [hν] at hf
    exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hf
  refine ⟨(integrable_map_measure hMap.aestronglyMeasurable hm.aemeasurable).mp hMap, ?_⟩
  rw [hν]
  change (∫ x, f x ∂(c : ℝ≥0∞) • ν.map chart) = _
  rw [integral_smul_measure, integral_map hm.aemeasurable hMap.aestronglyMeasurable,
    ENNReal.coe_toReal, Complex.real_smul]

private theorem detPower_inclusion (g : H) (s : ℂ) : P (A g) s = P g s := by
  unfold ArchimedeanLocal.detPower
  rw [det_rankInclusion]

private theorem characterWeight_tailWeyl (d : ComplexCharacterData) (s : ℂ) :
    characterWeight d s (determinant (tailWeyl k (q + 2))) =
      (d.character (determinant (weylLong (q + 2) ℂ)) : ℂ) := by
  change (d.character (determinant (tailWeyl k (q + 2))) : ℂ) * normPower s (determinant (tailWeyl k (q + 2))) = _
  rw [normPower_determinant, determinant_tailWeyl]
  simp only [ArchimedeanLocal.detPower, normalizedAbs_det_tailWeyl, Real.log_one,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- The normalized ordinary and dual restrictions with the same Haar factor. -/
def ComplexGapNormalizedRestrictionStatement : Prop :=
  ∀ (_hk : 0 < k) (a : ℂˣ) (κ : Measure Compact), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ c : ℝ≥0, 0 < c ∧
      let μ := complexSelfDualMeasure a
      let η := entryHaar μ (q + 1)
      let σ := unitOuterMeasure k q μ κ
      let Haar := complexGeneralLinearHaar (k + q + 1)
      (∀ (ds : List ComplexCharacterData) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
        (T : GodementColumnFactors k q), (∀ X, Φ X = T.eval k q X) →
        ∀ (W : complexWhittakerModel (k + q) ds (-a)) (g : H) (s : ℂ),
          let F := unitOrdinaryKernel k q a d T W.val g s
          Integrable (fun p => ∫ Z, F p Z ∂η) σ ∧
          continuedValue Haar μ d a Φ W.val (pad (A g) * tailWeyl k (q + 2)) s =
            (d.character (determinant (weylLong (q + 2) ℂ)) : ℂ) *
            (d.character ((-1 : ℂˣ) ^ (k + q + 1)) : ℂ) * P g (1 / 2) * (c : ℂ) *
              ∫ p, (∫ Z, F p Z ∂η) ∂σ) ∧
      (∀ (ds : List ComplexCharacterData) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
        (Wd : complexWhittakerModel (k + q) ds a) (g : H) (s : ℂ) (X : FullLower),
          let ρ := σ.prod ((rectangularMeasure μ q k).prod η)
          let F := unitDualKernel k q a d Φ Wd.val g s X
          Integrable F ρ ∧
          continuedValue Haar μ d.inv (-a) (rectTransform a Φ) Wd.val (pad (A g * lowerShear k q X)) (-s) =
            (d.inv.character ((-1 : ℂˣ) ^ (k + q + 1)) : ℂ) * P g (1 / 2) * (c : ℂ) * ∫ p, F p ∂ρ)

set_option maxHeartbeats 1200000 in
theorem complexGapNormalizedRestriction : ComplexGapNormalizedRestrictionStatement k q := by
  intro hk a κ hκ hκinv
  let μ := complexSelfDualMeasure a
  let η := entryHaar μ (q + 1)
  let σ := unitOuterMeasure k q μ κ
  let Haar := complexGeneralLinearHaar (k + q + 1)
  let ξ := (rectangularMeasure μ k q).prod η
  let ξd := (rectangularMeasure μ q k).prod η
  let : κ.IsHaarMeasure := hκ
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SigmaFinite (outerMeasure k q μ κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite σ := SigmaFinite.withDensity _
  let : ∀ n, SecondCountableTopology (GLc n) := gapGLSecondCountable
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology N := (Langlands.GeneralLinear.upperEntryCoordinates (K := ℂ) (q + 1)).secondCountableTopology
  obtain ⟨c, hc, ho, hd⟩ := complexGapDualChart k q hk μ κ hκ hκinv
  refine ⟨c, hc, ?_, ?_⟩
  · intro ds d Φ T hΦ W g s
    let b := tailWeyl k (q + 2)
    let Ψ := rightTest b Φ
    let T' := reverseTail k q T
    let Q := paddedRestrictionKernel μ d a Ψ W.val (A g) 1 s
    let F := unitOrdinaryKernel k q a d T W.val g s
    let chart := unitDeterminantChart k q
    have hm : Measurable chart := (continuous_unitDeterminantChart k q).measurable
    obtain ⟨hQ, hv⟩ := complexGodementPaddedRestriction (k + q) ds a Haar
      (by infer_instance) (by infer_instance) μ d Ψ W (A g) 1 s
    obtain ⟨hComp, hPull⟩ := pullback_integral (c := c) hm hc ho hQ
    have hFiber (p : Outer k q) : (∫ u, Q (chart (p, u)) ∂ξ) = ∫ Z, F p Z ∂η := by
      let B := unitRetained k q p
      have hB : complexNormalizedAbs B.val.det = 1 := normalizedAbs_unitRetained k q hk p
      obtain ⟨_, _, hi⟩ := complexGapTailExchange k q a (T'.partial k q a) ds W (restrictionWeight k q d s)
        g p.1.1.1 B
      have hEq : (fun u : Remainder => Q (chart (p, u))) =
          ordinaryBlockTailKernel k q (T'.partial k q a) W.val (restrictionWeight k q d s) g p.1.1.1 B :=
        funext fun u => paddedRestrictionKernel_split k q a d Ψ T' (rightTest_tailWeyl_eval k q Φ T hΦ)
          W.val g p.1.1.1 B u s
      rw [hEq, hi, hB, inv_one, Complex.ofReal_one, one_pow, one_mul]
      rfl
    refine ⟨?_, ?_⟩
    · change Integrable (fun p => ∫ Z, F p Z ∂η) σ
      simp_rw [← hFiber]
      exact hComp.integral_prod_left
    · have hInt : (∫ x, Q x ∂Haar) = (c : ℂ) * ∫ p, (∫ Z, F p Z ∂η) ∂σ :=
        hPull.trans (congrArg ((c : ℂ) * ·) ((integral_prod (fun p => Q (chart p)) hComp).trans
          (congrArg (fun f : Outer k q → ℂ => ∫ p, f p ∂σ) (funext hFiber))))
      rw [mul_one, map_one, map_one, mul_one] at hv
      rw [continuedValue_mul_right, hv, detPower_inclusion k q]
      change _ * (_ * _ * (∫ h, Q h ∂Haar)) = _
      rw [hInt]
      refine (congrArg (fun z : ℂ => z * _) (characterWeight_tailWeyl k q d _)).trans ?_
      ring
  · intro ds d Φ Wd g s X
    let b := lowerShear k q X
    let Ψ := rectTransform a Φ
    let Q := paddedRestrictionKernel μ d.inv (-a) Ψ Wd.val (A g) b (-s)
    let chart := dualChart k q
    have hWd : Wd.val ∈ complexWhittakerModel (k + q) ds (-(-a)) := by simpa only [neg_neg] using Wd.2
    obtain ⟨hQ, hv⟩ := complexGodementPaddedRestriction (k + q) ds (-a) Haar
      (by infer_instance) (by infer_instance) μ d.inv Ψ ⟨Wd.val, hWd⟩ (A g) b (-s)
    obtain ⟨hI, hInt⟩ := pullback_integral (c := c) (measurable_dualChart k q) hc hd hQ
    have hF : (Q ∘ chart) = unitDualKernel k q a d Φ Wd.val g s X := rfl
    refine ⟨hF ▸ hI, ?_⟩
    have hb : determinant b = 1 := determinant_lowerShear k q X
    rw [hb, map_one, mul_one, detPower_inclusion k q] at hv
    rw [hv]
    change _ * _ * (∫ h, Q h ∂Haar) = _
    rw [hInt]
    simp only [mul_assoc]
    rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGapNormalizedRestriction
