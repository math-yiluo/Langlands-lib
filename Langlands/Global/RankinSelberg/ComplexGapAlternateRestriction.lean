import Langlands.Global.RankinSelberg.ComplexGapTailExchange
import Langlands.Global.RankinSelberg.ComplexGapTriangularChart
import Langlands.Global.RankinSelberg.ComplexGodementPaddedRestriction

/-! # The alternate split Godement integral in the larger rank difference -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (rankInclusion determinant blockSum_apply_right blockSum_apply_right_left)
open Langlands.HarmonicAnalysis (rectangularJoin rectangularJoin_castSucc rectangularJoin_last
  partialFourierPlusIntegral_join)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open Langlands.RankinSelberg (rectangularMeasure lastRow_mul_eq_vecMul det_rankInclusion)
open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure)
open ComplexGapTailExchange
open ComplexGapTriangularChart (Outer outerMeasure retainedMatrix triangularRightChart continuous_triangularRightChart
  diagonalWeightMeasure)
open ComplexGapUpperTail (packedTail laterRectangle)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementPaddedRestriction (paddedRestrictionKernel complexGodementPaddedRestriction)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance gapGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

open scoped Matrix.Norms.Operator in
private theorem gapGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable (k q : ℕ)

local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "Vec" => I → ℂ
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℂ
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "Compact" => unitaryCompact ℂ (k + q + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "Remainder" => Matrix (Fin k) (Fin q) ℂ × N
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

/-- A split matrix test has a leading rectangular factor and one Schwartz factor for each tail column. -/
structure GodementColumnFactors where
  leading : 𝓢(Matrix I (Fin k) ℂ, ℂ)
  tail : Fin (q + 2) → 𝓢(Vec, ℂ)

/-- Evaluate the column factors before applying any Fourier transforms. -/
def GodementColumnFactors.eval (T : GodementColumnFactors k q) (X : Rect) : ℂ :=
  T.leading (fun i j => X i (j.castAdd (q + 2))) *
    ∏ j : Fin (q + 2), T.tail j (fun i => X i (j.natAdd k))

/-- The factors in the partially transformed matrix test. -/
def GodementColumnFactors.partial (T : GodementColumnFactors k q) (a : ℂˣ) : SplitTailTest k q where
  leading := T.leading
  first := T.tail 0
  later j := T.tail j.succ.castSucc
  lastFrequency := ComplexGodementFourier.fourier a (T.tail (Fin.last (q + 1)))

private theorem eval_join (T : GodementColumnFactors k q) (A : Matrix I I ℂ) (v : Vec) :
    T.eval k q (rectangularJoin A v) =
      (T.leading (fun i j => A i (j.castAdd (q + 1))) *
        T.tail 0 (fun i => A i ((0 : J).natAdd k)) *
        ∏ j : Fin q, T.tail j.succ.castSucc (fun i => A i (j.succ.natAdd k))) *
        T.tail (Fin.last (q + 1)) v := by
  unfold GodementColumnFactors.eval
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
  have hlead (j : Fin k) : j.castAdd (q + 2) = (j.castAdd (q + 1)).castSucc := Fin.ext rfl
  have htail (j : J) : j.castSucc.natAdd k = (j.natAdd k).castSucc := Fin.ext rfl
  have hlast : (Fin.last (q + 1)).natAdd k = Fin.last (k + q + 1) := Fin.ext rfl
  have hzero : (0 : Fin (q + 2)).natAdd k = ((0 : J).natAdd k).castSucc := Fin.ext rfl
  simp only [hlead, htail, hlast, Fin.castSucc_zero, hzero, rectangularJoin_castSucc, rectangularJoin_last,
    mul_assoc]

/-- Partial Fourier transformation of a split test in its last column. -/
theorem partial_join (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q)
    (hΦ : ∀ X, Φ X = T.eval k q X) (A : Matrix I I ℂ) (v : Vec) :
    partialSchwartz a (complexSelfDualMeasure a) Φ (rectangularJoin A v) =
      (T.leading (fun i j => A i (j.castAdd (q + 1))) *
        T.tail 0 (fun i => A i ((0 : J).natAdd k)) *
        ∏ j : Fin q, T.tail j.succ.castSucc (fun i => A i (j.succ.natAdd k))) *
        ComplexGodementFourier.fourier a (T.tail (Fin.last (q + 1))) v := by
  rw [partialSchwartz_apply, partialFourierPlusIntegral_join, ComplexGodementFourier.fourier, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hΦ, eval_join, ComplexGodementFourier.psi, mul_assoc, mul_comm (v _) (x _)]

private theorem lastRow_rankInclusion (h : H) :
    Langlands.RankinSelberg.lastRow (rankInclusion (q + 1) h) = Langlands.RankinSelberg.lastRow (1 : G) := by
  have hl : (Fin.last q).natAdd k = Fin.last (k + q) := Fin.ext rfl
  funext j
  change (rankInclusion (q + 1) h).val (Fin.last (k + q)) j = (1 : Matrix I I ℂ) (Fin.last (k + q)) j
  rw [← hl]
  refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [show (rankInclusion (q + 1) h).val ((Fin.last q).natAdd k) (j₀.castAdd (q + 1)) = 0 from
      blockSum_apply_right_left h 1 (Fin.last q) j₀]
    rw [Matrix.one_apply_ne]
    intro he
    have he' := congrArg Fin.val he
    change k + q = j₀.val at he'
    omega
  · rw [show (rankInclusion (q + 1) h).val ((Fin.last q).natAdd k) (j₁.natAdd k) =
      (1 : Matrix J J ℂ) (Fin.last q) j₁ from blockSum_apply_right h 1 (Fin.last q) j₁,
      Matrix.one_apply, Matrix.one_apply]
    congr 1
    exact propext ⟨fun e => congrArg (Fin.natAdd k) e, fun e => Fin.ext (by simpa using congrArg Fin.val e)⟩

private theorem tailColumn_rankInclusion (C : G) (h : H) (j : J) :
    (fun i : I => (C * rankInclusion (q + 1) h).val i (j.natAdd k)) = fun i => C.val i (j.natAdd k) := by
  have hc : (fun i : I => (rankInclusion (q + 1) h).val i (j.natAdd k)) =
      fun i => (1 : Matrix I I ℂ) i (j.natAdd k) := by
    funext i
    refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
    · rw [show (rankInclusion (q + 1) h).val (i₀.castAdd (q + 1)) (j.natAdd k) = 0 from
        Langlands.GeneralLinear.blockSum_apply_left_right h 1 i₀ j, Matrix.one_apply_ne]
      intro e
      have he := congrArg Fin.val e
      change i₀.val = k + j.val at he
      omega
    · rw [show (rankInclusion (q + 1) h).val (i₁.natAdd k) (j.natAdd k) = (1 : Matrix J J ℂ) i₁ j from
          blockSum_apply_right h 1 i₁ j,
        Matrix.one_apply, Matrix.one_apply]
      congr 1
      exact propext ⟨fun e => congrArg (Fin.natAdd k) e, fun e => Fin.ext (by simpa using congrArg Fin.val e)⟩
  change C.val.mulVec (fun i => (rankInclusion (q + 1) h).val i (j.natAdd k)) = _
  rw [hc]
  change (fun i => (C.val * (1 : Matrix I I ℂ)) i (j.natAdd k)) = _
  rw [Matrix.mul_one]

/-- The adjoining character and determinant exponent in the changed Godement variable. -/
def restrictionWeight (d : ComplexCharacterData) (s : ℂ) : ℂˣ →* ℂ :=
  characterWeight d (((k + q + 2 : ℕ) : ℂ) / 2 + s - 1)

/-- Pointwise identification on a chart with any retained matrix. -/
theorem paddedRestrictionKernel_split (a : ℂˣ) (d : ComplexCharacterData)
    (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q) (hΦ : ∀ X, Φ X = T.eval k q X)
    (W : G → ℂ) (g h : H) (B : G) (p : Remainder) (s : ℂ) :
    paddedRestrictionKernel (complexSelfDualMeasure a) d a Φ W (rankInclusion (q + 1) g) 1 s
        (B * (packedTail k q (laterRectangle k q p.1) p.2).val * rankInclusion (q + 1) h) =
      ordinaryBlockTailKernel k q (T.partial k q a) W (restrictionWeight k q d s) g h B p := by
  let C := B * (packedTail k q (laterRectangle k q p.1) p.2).val
  let A : G := rankInclusion (q + 1) h
  let g₀ : G := rankInclusion (q + 1) g
  let χ := restrictionWeight k q d s
  have hW : g₀ * (C * A)⁻¹ = rankInclusion (q + 1) (g * h⁻¹) * C⁻¹ := by
    simp only [A, g₀, mul_inv_rev, map_mul, map_inv, mul_assoc]
  have hRow : Langlands.RankinSelberg.lastRow (g₀ * (C * A)⁻¹) = Langlands.RankinSelberg.lastRow C⁻¹ := by
    rw [hW, lastRow_mul_eq_vecMul, lastRow_rankInclusion k q, ← lastRow_mul_eq_vecMul, one_mul]
  have hdet : determinant A = determinant h := Units.ext (det_rankInclusion (q + 1) h)
  have hWeight : χ (determinant (C * A)) = χ (determinant C) * χ (determinant h) := by
    rw [map_mul determinant, map_mul χ]
    exact congrArg (fun z => χ (determinant C) * χ z) hdet
  unfold paddedRestrictionKernel
  change partialSchwartz a (complexSelfDualMeasure a) Φ
      (rectangularJoin ((C * A).val * (1 : Matrix I I ℂ)) (Langlands.RankinSelberg.lastRow (g₀ * (C * A)⁻¹))) *
      W (g₀ * (C * A)⁻¹) * χ (determinant (C * A)) = _
  rw [Matrix.mul_one, hRow, hW, hWeight, partial_join k q a Φ T hΦ]
  simp only [A, tailColumn_rankInclusion]
  unfold ordinaryBlockTailKernel fixedTailFactor GodementColumnFactors.partial
  change _ = (T.leading (fun i j => (C * A).val i (j.castAdd (q + 1))) *
    T.tail 0 (fun i => C.val i ((0 : J).natAdd k)) *
    ComplexGodementFourier.fourier a (T.tail (Fin.last (q + 1))) (Langlands.RankinSelberg.lastRow C⁻¹) *
    W (rankInclusion (q + 1) (g * h⁻¹) * C⁻¹) * χ (determinant h) * χ (determinant C)) *
    ∏ j : Fin q, T.tail j.succ.castSucc (fun i => C.val i (j.succ.natAdd k))
  ring

/-- The alternate kernel after Fourier transformation in the later columns, with its Jacobian. -/
def alternateRestrictionKernel (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (W : G → ℂ) (g : H) (s : ℂ) (p : Outer k q) (Z : N) : ℂ :=
  let B := retainedMatrix k q p
  (((complexNormalizedAbs B.val.det)⁻¹ : ℝ) : ℂ) ^ q *
    alternateBlockTailKernel k q a (T.partial k q a) W (restrictionWeight k q d s) g p.1.1.1 B Z

/-- The alternate split formula for the continued Godement value at a padded leading matrix. -/
def ComplexGapAlternateRestrictionStatement : Prop :=
  ∀ (_hk : 0 < k) (a : ℂˣ) (κ : Measure Compact), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ c : ℝ≥0, 0 < c ∧
    ∀ (ds : List ComplexCharacterData) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
      (T : GodementColumnFactors k q), (∀ X, Φ X = T.eval k q X) →
    ∀ (W : complexWhittakerModel (k + q) ds (-a)) (g : H) (s : ℂ),
      let μ := complexSelfDualMeasure a
      let η := entryHaar μ (q + 1)
      let σ := outerMeasure k q μ κ
      let Haar := complexGeneralLinearHaar (k + q + 1)
      let F := alternateRestrictionKernel k q a d T W.val g s
      (∀ p, Integrable (F p) η) ∧ Integrable (fun p => ∫ Z, F p Z ∂η) σ ∧
      continuedValue Haar μ d a Φ W.val (padGL (Nat.le_succ (k + q + 1)) (rankInclusion (q + 1) g)) s =
        (d.character ((-1 : ℂˣ) ^ (k + q + 1)) : ℂ) * P g (1 / 2) * (c : ℂ) *
          ∫ p, (∫ Z, F p Z ∂η) ∂σ

set_option maxHeartbeats 800000 in
theorem complexGapAlternateRestriction : ComplexGapAlternateRestrictionStatement k q := by
  intro hk a κ hκ hκinv
  let μ := complexSelfDualMeasure a
  let η := entryHaar μ (q + 1)
  let σ := outerMeasure k q μ κ
  let ξ := (rectangularMeasure μ k q).prod η
  let Haar := complexGeneralLinearHaar (k + q + 1)
  let : κ.IsHaarMeasure := hκ
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SigmaFinite (diagonalWeightMeasure k q) := inferInstance
  let : SecondCountableTopology N := (Langlands.GeneralLinear.upperEntryCoordinates (K := ℂ) (q + 1)).secondCountableTopology
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : ∀ n, SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
    gapGLSecondCountable
  let : SigmaFinite σ := by
    unfold σ outerMeasure
    infer_instance
  let chart := triangularRightChart k q
  have hChart : Measurable chart := (continuous_triangularRightChart k q).measurable
  obtain ⟨c, hc, hHaar⟩ := ComplexGapTriangularChart.complexGapTriangularChart k q hk μ κ hκ hκinv
  change Haar = c • (σ.prod ξ).map chart at hHaar
  refine ⟨c, hc, ?_⟩
  intro ds d Φ T hΦ W g s
  let g₀ : G := rankInclusion (q + 1) g
  let Q := paddedRestrictionKernel μ d a Φ W.val g₀ 1 s
  let F := alternateRestrictionKernel k q a d T W.val g s
  obtain ⟨hQ, hValue⟩ := complexGodementPaddedRestriction (k + q) ds a Haar
    (by infer_instance) (by infer_instance) μ d Φ W g₀ 1 s
  change Integrable Q Haar at hQ
  have hMap : Integrable Q ((σ.prod ξ).map chart) := by
    rw [hHaar] at hQ
    exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hQ
  have hComp : Integrable (Q ∘ chart) (σ.prod ξ) :=
    (integrable_map_measure hMap.aestronglyMeasurable hChart.aemeasurable).mp hMap
  have hFiber (p : Outer k q) : Integrable (F p) η ∧
      (∫ u, Q (chart (p, u)) ∂ξ) = ∫ Z, F p Z ∂η := by
    obtain ⟨_, hI, hi⟩ := complexGapTailExchange k q a (T.partial k q a) ds W (restrictionWeight k q d s)
      g p.1.1.1 (retainedMatrix k q p)
    refine ⟨hI.const_mul _, ?_⟩
    simp only [show (fun u => Q (chart (p, u))) = ordinaryBlockTailKernel k q (T.partial k q a)
      W.val (restrictionWeight k q d s) g p.1.1.1 (retainedMatrix k q p) from
        funext fun u => paddedRestrictionKernel_split k q a d Φ T hΦ W.val g p.1.1.1 (retainedMatrix k q p) u s]
    rw [hi]
    exact (integral_const_mul _ _).symm
  have hIntegrable : Integrable (fun p => ∫ Z, F p Z ∂η) σ := by
    simp_rw [← (hFiber _).2]
    exact hComp.integral_prod_left
  have hInt : (∫ h, Q h ∂Haar) = (c : ℂ) * ∫ p, (∫ Z, F p Z ∂η) ∂σ := by
    rw [hHaar]
    change (∫ h, Q h ∂(c : ℝ≥0∞) • (σ.prod ξ).map chart) = _
    rw [integral_smul_measure, integral_map hChart.aemeasurable hMap.aestronglyMeasurable,
      ENNReal.coe_toReal, Complex.real_smul, integral_prod (fun x => Q (chart x)) hComp]
    simp_rw [(hFiber _).2]
  refine ⟨fun p => (hFiber p).1, hIntegrable, ?_⟩
  rw [mul_one] at hValue
  rw [hValue, map_one, map_one, mul_one]
  change _ * _ * (∫ h, Q h ∂Haar) = _
  rw [hInt, show P g₀ (1 / 2) = P g (1 / 2) by
    unfold ArchimedeanLocal.detPower
    rw [det_rankInclusion]]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateRestriction
