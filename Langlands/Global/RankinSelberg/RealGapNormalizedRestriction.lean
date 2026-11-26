import Langlands.Global.RankinSelberg.RealGapMatchedTests

/-! # Ordinary and dual real Godement restrictions with one Haar constant -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapNormalizedRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (rankInclusion determinant weylLong)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.RankinSelberg (rectangularMeasure det_rankInclusion)
open ArchimedeanLocal (realSelfDualMeasure realNormalizedAbs RealQuotientMeasureData)
open RealJacquet (realAdjacentGodementCoefficient realAdjacentWeylSign detCharacter joinLastColumn
  realColumnProduct)
open RealGapAlternateRestriction (GodementColumnFactors restrictionWeight paddedRestrictionKernel_split)
open RealGapDualChart (retainedTail dualChart measurable_dualChart lowerShear determinant_lowerShear
  realGapDualChart)
open RealGapMatchedTests (dualFiber)
open RealGapTailExchange (alternateBlockTailKernel ordinaryBlockTailKernel realGapTailExchange
  LeftWhittakerEquivariant)
open RealGapTriangularChart (Outer outerMeasure)
open RealGapUnitDeterminant (unitRetained unitDeterminantChart unitOuterMeasure normalizedAbs_unitRetained
  continuous_unitDeterminantChart)
open RealGapWeylRestriction (tailWeyl reverseTail realAdjacentGodementCoefficient_mul_right
  rectangularTranslate_tailWeyl determinantWeight_tailWeyl)
open RealGodement (realRectangularSchwartzFourier realRowSchwartzFourier rectangularTranslate)
open RealGodementPaddedRestriction (paddedRestrictionKernel realGodementPaddedRestriction
  realColumnProduct_joinLastColumn)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

local notation "GLr" => fun n => Langlands.GeneralLinear n ℝ
local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (GLr n) := borel _
local instance gapGLBorel (n : ℕ) : BorelSpace (GLr n) := ⟨rfl⟩
local instance gapGLSecondCountable (n : ℕ) : SecondCountableTopology (GLr n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapNUMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance gapNUBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
local instance gapQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _

variable (k q : ℕ)
local notation "G" => GLr (k + q + 1)
local notation "H" => GLr k
local notation "A" => rankInclusion (R := ℝ) (n := k) (q + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℝ
local notation "Remainder" => Matrix (Fin k) (Fin q) ℝ × N
local notation "DualRemainder" => Matrix (Fin q) (Fin k) ℝ × N
local notation "FullLower" => Matrix (Fin (q + 1)) (Fin k) ℝ
local notation "I" => Fin (k + q + 1)
local notation "Sq" => Matrix I I ℝ
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℝ
local notation "Compact" => unitaryCompact ℝ (k + q + 1)
local notation "pad" => padGL (Nat.succ_le_succ (Nat.le_succ (k + q)))
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

/-- The alternate ordinary split kernel on the determinant-normalized chart. -/
def unitOrdinaryKernel (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (U : G → ℂ) (g : H) (p : Outer k q) (Z : N) : ℂ :=
  alternateBlockTailKernel k q a ((reverseTail k q T).partial k q a) U (restrictionWeight k q c)
    g p.1.1.1 (unitRetained k q p) Z

/-- The full dual kernel in the dual chart, with the outer complementary rectangle fixed. -/
def unitDualKernel (a : ℝˣ) (c : RealCharacterData) (F : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q)
    (Ud : G → ℂ) (g : H) (X : FullLower) (p : Outer k q × DualRemainder) : ℂ :=
  dualFiber k q a c F T Ud g p.1.1.1.1 (retainedTail k q p.1 p.2.2) p.2.1 X

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

private theorem detCharacter_one (c : RealCharacterData) {n : ℕ} :
    detCharacter c.character.toMonoidHom (1 : GLr n) = 1 := by
  simp [detCharacter]

private theorem detPower_one {n : ℕ} (s : ℂ) : P (1 : GLr n) s = 1 := by
  simp [ArchimedeanLocal.detPower, realNormalizedAbs]

private theorem detCharacter_of_det_one (c : RealCharacterData) {n : ℕ} (b : GLr n)
    (hb : determinant b = 1) : detCharacter c.character.toMonoidHom b = 1 := by
  unfold detCharacter
  rw [hb, map_one, Units.val_one]

private theorem detPower_of_det_one {n : ℕ} (b : GLr n) (hb : determinant b = 1) (s : ℂ) :
    P b s = 1 := by
  have hd : b.val.det = 1 := congrArg Units.val hb
  simp [ArchimedeanLocal.detPower, realNormalizedAbs, hd]

/-- The normalized ordinary and dual restrictions with the same Haar factor. -/
def RealGapNormalizedRestrictionStatement : Prop :=
  ∀ (_hk : 0 < k) (a : ℝˣ) (D' : RealQuotientMeasureData (k + q)) (η₁ : Measure H)
    (κ : Measure Compact), η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ C : ℝ≥0, 0 < C ∧
      let μ := realSelfDualMeasure a
      let η := entryHaar μ (q + 1)
      let σ := unitOuterMeasure k q μ η₁ κ
      (∀ (ds : List RealBlock) (c : RealCharacterData) (T : GodementColumnFactors k q)
        (Φ : 𝓢(Rect, ℂ)),
        (∀ B x, Φ (joinLastColumn B x) = T.squareEval k q B * T.tail (Fin.last (q + 1)) x) →
        ∀ (U : G → ℂ), U ∈ realUniformWhittakerModel (k + q) ds (-a) → ∀ g : H,
          let F := unitOrdinaryKernel k q a c T U g
          Integrable (fun p => ∫ Z, F p Z ∂η) σ ∧
          realAdjacentGodementCoefficient D' a Φ U c (pad (A g) * tailWeyl k (q + 2)) =
            detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) * realAdjacentWeylSign (k + q) c *
              P g (1 / 2) * (C : ℂ) * ∫ p, (∫ Z, F p Z ∂η) ∂σ) ∧
      (∀ (ds : List RealBlock) (c : RealCharacterData) (F : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q),
        (∀ B, F B = T.squareEval k q B) →
        ∀ (Ud : G → ℂ), Ud ∈ realUniformWhittakerModel (k + q) ds a → ∀ (g : H) (X : FullLower),
          let ρ := σ.prod ((rectangularMeasure μ q k).prod η)
          let Fd := unitDualKernel k q a c F T Ud g X
          Integrable Fd ρ ∧
          realAdjacentGodementCoefficient D' (-a)
              (realColumnProduct (realRectangularSchwartzFourier a F)
                (realRowSchwartzFourier (k + q + 1) a (T.tail (Fin.last (q + 1))))) Ud c.inverse
              (pad (A g * lowerShear k q X)) =
            realAdjacentWeylSign (k + q) c.inverse * P g (1 / 2) * (C : ℂ) * ∫ p, Fd p ∂ρ)

set_option maxHeartbeats 1200000 in
theorem realGapNormalizedRestriction : RealGapNormalizedRestrictionStatement k q := by
  intro hk a D' η₁ κ hη₁ hκ hκinv
  let μ := realSelfDualMeasure a
  let η := entryHaar μ (q + 1)
  let σ := unitOuterMeasure k q μ η₁ κ
  let Haar := D'.groupHaar
  let : Haar.IsHaarMeasure := D'.groupHaar_isHaar
  let ξ := (rectangularMeasure μ k q).prod η
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology N :=
    (Langlands.GeneralLinear.upperEntryCoordinates (K := ℝ) (q + 1)).secondCountableTopology
  let : SigmaFinite (outerMeasure k q μ η₁ κ) := by unfold outerMeasure; infer_instance
  let : SigmaFinite σ := SigmaFinite.withDensity _
  obtain ⟨C, hC, ho, hd⟩ := realGapDualChart k q hk μ Haar η₁ κ inferInstance hη₁ hκ hκinv
  refine ⟨C, hC, ?_, ?_⟩
  · intro ds c T Φ hΦ U hU g
    let b := tailWeyl k (q + 2)
    let Ψ := rectangularTranslate 1 b Φ
    let T' := reverseTail k q T
    let Q := paddedRestrictionKernel c a (T'.squareEval k q) (T'.tail (Fin.last (q + 1))) U (A g) 1
    let F := unitOrdinaryKernel k q a c T U g
    let chart := unitDeterminantChart k q
    have hm : Measurable chart := (continuous_unitDeterminantChart k q).measurable
    obtain ⟨hQ, hv⟩ := realGodementPaddedRestriction (k + q) ds a D' c Ψ (T'.squareEval k q)
      (T'.tail (Fin.last (q + 1))) (rectangularTranslate_tailWeyl k q Φ T hΦ) U hU (A g) 1
    obtain ⟨hComp, hPull⟩ := pullback_integral (c := C) hm hC ho hQ
    have hUeq : LeftWhittakerEquivariant k q a U :=
      fun u hu x => ((realUniformWhittakerRegularity (k + q) ds (-a) U hU).1 []).1 u hu x
    have hFiber (p : Outer k q) : (∫ u, Q (chart (p, u)) ∂ξ) = ∫ Z, F p Z ∂η := by
      let B := unitRetained k q p
      have hB : realNormalizedAbs B.val.det = 1 := normalizedAbs_unitRetained k q hk p
      obtain ⟨_, _, hi⟩ := realGapTailExchange k q a (T'.partial k q a) U hUeq (restrictionWeight k q c)
        g p.1.1.1 B
      have hEq : (fun u : Remainder => Q (chart (p, u))) =
          ordinaryBlockTailKernel k q (T'.partial k q a) U (restrictionWeight k q c) g p.1.1.1 B :=
        funext fun u => paddedRestrictionKernel_split k q a c T' (T'.squareEval k q) (fun _ => rfl)
          U g p.1.1.1 B u
      rw [hEq, hi, hB, inv_one, Complex.ofReal_one, one_pow, one_mul]
      rfl
    refine ⟨?_, ?_⟩
    · change Integrable (fun p => ∫ Z, F p Z ∂η) σ
      simp_rw [← hFiber]
      exact hComp.integral_prod_left
    · have hInt : (∫ x, Q x ∂Haar) = (C : ℂ) * ∫ p, (∫ Z, F p Z ∂η) ∂σ :=
        hPull.trans (congrArg ((C : ℂ) * ·) ((integral_prod (fun p => Q (chart p)) hComp).trans
          (congrArg (fun f : Outer k q → ℂ => ∫ p, f p ∂σ) (funext hFiber))))
      rw [mul_one] at hv
      have hw : RealGodement.determinantWeight c ((((k + q : ℕ) : ℂ) + 1) / 2)
          (tailWeyl k (q + 2) : Langlands.GeneralLinear (k + q + 2) ℝ) =
          detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) :=
        determinantWeight_tailWeyl c _ k (q + 2)
      rw [realAdjacentGodementCoefficient_mul_right, hv, detCharacter_one, detPower_one,
        detPower_inclusion k q]
      change _ * (_ * _ * _ * _ * (∫ h, Q h ∂Haar)) = _
      rw [hInt]
      refine (congrArg (fun z : ℂ => z * _) hw).trans ?_
      ring
  · intro ds c F T hF Ud hUd g X
    let bX := lowerShear k q X
    let Fh := realRectangularSchwartzFourier a F
    let fh := realRowSchwartzFourier (k + q + 1) a (T.tail (Fin.last (q + 1)))
    let Q := paddedRestrictionKernel c.inverse (-a) Fh fh Ud (A g) bX
    let chart := dualChart k q
    have hUd' : Ud ∈ realUniformWhittakerModel (k + q) ds (-(-a)) := by simpa only [neg_neg] using hUd
    obtain ⟨hQ, hv⟩ := realGodementPaddedRestriction (k + q) ds (-a) D' c.inverse
      (realColumnProduct Fh fh) Fh fh (realColumnProduct_joinLastColumn Fh fh) Ud hUd' (A g) bX
    obtain ⟨hI, hInt⟩ := pullback_integral (c := C) (measurable_dualChart k q) hC hd hQ
    have hFk : (Q ∘ chart) = unitDualKernel k q a c F T Ud g X := rfl
    refine ⟨hFk ▸ hI, ?_⟩
    have hb : determinant bX = 1 := determinant_lowerShear k q X
    rw [detCharacter_of_det_one c.inverse bX hb, detPower_of_det_one bX hb, mul_one, mul_one,
      detPower_inclusion k q] at hv
    rw [hv]
    change _ * _ * (∫ h, Q h ∂Haar) = _
    rw [hInt]
    simp only [mul_assoc]
    rfl

end Langlands.Global.RankinSelbergGlobal.RealGapNormalizedRestriction
