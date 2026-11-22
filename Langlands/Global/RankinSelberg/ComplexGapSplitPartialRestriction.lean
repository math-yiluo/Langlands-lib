import Langlands.Global.RankinSelberg.ComplexGapTailExchange
import Langlands.Global.RankinSelberg.ComplexGapTriangularChart
import Langlands.Global.RankinSelberg.ComplexGodementPaddedRestriction
import Langlands.Representation.RankinSelberg.TwistInvariance

/-! # The alternate restriction of a complex Godement value -/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise SchwartzMap NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSplitPartialRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (rankInclusion determinant blockSum blockSum_apply_right_left
  blockSum_apply_left_right blockSum_apply_right)
open Langlands.HarmonicAnalysis (rectangularJoin)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar det_rankInclusion)
open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure)
open ComplexGapTailExchange (SplitTailTest ordinaryBlockTailKernel alternateBlockTailKernel
  fixedTailFactor complexGapTailExchange)
open ComplexGapTriangularChart (Outer outerMeasure retainedMatrix triangularRightChart
  complexGapTriangularChart continuous_triangularRightChart)
open ComplexGapUpperTail (packedTail laterRectangle)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementPaddedRestriction (paddedRestrictionKernel complexGodementPaddedRestriction)
open ComplexGodementPartialFourier (partialSchwartz)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

variable (k q : ℕ)

local notation "Size" => (k + q + 1)
local notation "Order" => (k + q)
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "K" => unitaryCompact ℂ (k + q + 1)
local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "Square" => Matrix I I ℂ
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℂ
local notation "Tail" => Matrix (Fin k) (Fin q) ℂ
local notation "iSmall" => (rankInclusion (q + 1) : H →* G)
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

local instance alternateRestrictionGLMeasurable (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear m ℂ) :=
  borel _
local instance alternateRestrictionGLBorel (m : ℕ) : BorelSpace (Langlands.GeneralLinear m ℂ) := ⟨rfl⟩
local instance alternateRestrictionTailMeasurable : MeasurableSpace N := borel _
local instance alternateRestrictionTailBorel : BorelSpace N := ⟨rfl⟩

private theorem rankInclusion_column (h : H) (j : J) :
    (fun i : I => (iSmall h).val i (j.natAdd k)) = fun i => (1 : Square) i (j.natAdd k) := by
  funext i
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [show (iSmall h).val (i₀.castAdd (q + 1)) (j.natAdd k) = 0 from
      blockSum_apply_left_right h (1 : Langlands.GeneralLinear (q + 1) ℂ) i₀ j]
    rw [Matrix.one_apply_ne]
    exact fun e => by have he := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at he; omega
  · change (blockSum (h, (1 : Langlands.GeneralLinear (q + 1) ℂ))).val
      (i₁.natAdd k) (j.natAdd k) = _
    rw [blockSum_apply_right, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff]

private theorem mul_rankInclusion_column (C : G) (h : H) (j : J) :
    (fun i : I => (C * iSmall h).val i (j.natAdd k)) = fun i => C.val i (j.natAdd k) := by
  change C.val.mulVec (fun i => (iSmall h).val i (j.natAdd k)) = _
  rw [rankInclusion_column k q h j]
  change (fun i => (C.val * (1 : Square)) i (j.natAdd k)) = _
  rw [Matrix.mul_one]

private theorem lastRow_rankInclusion_mul (g : H) (C : G) :
    Langlands.RankinSelberg.lastRow (iSmall g * C) = Langlands.RankinSelberg.lastRow C := by
  have hLast : (Fin.last q).natAdd k = Fin.last Order := Fin.ext rfl
  have hRow : (iSmall g).val (Fin.last Order) = (1 : Square) (Fin.last Order) := by
    rw [← hLast]
    funext i
    refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
    · rw [show (iSmall g).val ((Fin.last q).natAdd k) (i₀.castAdd (q + 1)) = 0 from
        blockSum_apply_right_left g (1 : Langlands.GeneralLinear (q + 1) ℂ) (Fin.last q) i₀]
      rw [Matrix.one_apply_ne]
      exact fun e => by have he := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at he; omega
    · change (blockSum (g, (1 : Langlands.GeneralLinear (q + 1) ℂ))).val
        ((Fin.last q).natAdd k) (i₁.natAdd k) = _
      rw [blockSum_apply_right, Units.val_one, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff]
  change (iSmall g).val (Fin.last Order) ᵥ* C.val = _
  rw [hRow]
  change (fun i => ((1 : Square) * C.val) (Fin.last Order) i) = _
  rw [Matrix.one_mul]
  rfl

/-- The partial Fourier test splits across the leading rectangle and the trailing columns. -/
def HasSplitPartialTest (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (T : SplitTailTest k q) : Prop :=
  ∀ (A : Square) (v : I → ℂ),
    partialSchwartz a (complexSelfDualMeasure a) Φ (rectangularJoin A v) =
      T.leading (fun i j => A i (j.castAdd (q + 1))) * T.first (fun i => A i ((0 : J).natAdd k)) *
        (∏ j : Fin q, T.later j (fun i => A i (j.succ.natAdd k))) * T.lastFrequency v

private theorem ordinaryKernel_eq (a : ℂˣ) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : 𝓢(Rect, ℂ)) (T : SplitTailTest k q) (hΦ : HasSplitPartialTest k q a Φ T)
    (W : complexWhittakerModel Order ds (-a)) (g : H) (s : ℂ) (p : Outer k q × (Tail × N)) :
    paddedRestrictionKernel (complexSelfDualMeasure a) d a Φ W.val (iSmall g) 1 s
        (triangularRightChart k q p) =
      ordinaryBlockTailKernel k q T W.val (characterWeight d (((Order + 2 : ℕ) : ℂ) / 2 + s - 1))
        g p.1.1.1.1 (retainedMatrix k q p.1) p.2 := by
  let B := retainedMatrix k q p.1
  let C := B * (packedTail k q (laterRectangle k q p.2.1) p.2.2).val
  let h := p.1.1.1.1
  let χ := characterWeight d (((Order + 2 : ℕ) : ℂ) / 2 + s - 1)
  have hArg : iSmall g * (C * iSmall h)⁻¹ = iSmall (g * h⁻¹) * C⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc]
    exact congrArg (· * C⁻¹) ((congrArg (iSmall g * ·) (map_inv iSmall h).symm).trans
      (map_mul iSmall g h⁻¹).symm)
  have hRow : (iSmall g * (C * iSmall h)⁻¹).val (Fin.last Order) = Langlands.RankinSelberg.lastRow C⁻¹ := by
    rw [hArg]
    exact lastRow_rankInclusion_mul k q (g * h⁻¹) C⁻¹
  have hdet : determinant (iSmall h) = determinant h := Units.ext (det_rankInclusion (q + 1) h)
  have hWeight : χ (determinant (C * iSmall h)) = χ (determinant h) * χ (determinant C) := by
    calc
      _ = χ (determinant C * determinant (iSmall h)) := congrArg χ (map_mul determinant _ _)
      _ = χ (determinant C * determinant h) := congrArg (fun z => χ (determinant C * z)) hdet
      _ = _ := (map_mul χ _ _).trans (mul_comm _ _)
  unfold paddedRestrictionKernel ordinaryBlockTailKernel fixedTailFactor
  change partialSchwartz a _ Φ (rectangularJoin ((C * iSmall h).val * (1 : G).val)
      ((iSmall g * (C * iSmall h)⁻¹).val (Fin.last Order))) *
      W.val (iSmall g * (C * iSmall h)⁻¹) * χ (determinant (C * iSmall h)) = _
  rw [Units.val_one, Matrix.mul_one, hRow, hArg, hΦ, hWeight]
  simp_rw [mul_rankInclusion_column k q C h]
  change _ = T.leading (fun i j => (C * iSmall h).val i (j.castAdd (q + 1))) *
    T.first (fun i => C.val i ((0 : J).natAdd k)) * T.lastFrequency (Langlands.RankinSelberg.lastRow C⁻¹) *
      W.val (iSmall (g * h⁻¹) * C⁻¹) * χ (determinant h) * χ (determinant C) *
      ∏ j : Fin q, T.later j (fun i => C.val i (j.succ.natAdd k))
  ring

/-- The exact alternate marginal of the fixed padded Godement value. -/
def ComplexGapSplitPartialRestrictionStatement : Prop :=
  ∀ (_hk : 0 < k) (a : ℂˣ) (κ : Measure K), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (d : ComplexCharacterData) (ds : List ComplexCharacterData)
      (Φ : 𝓢(Rect, ℂ)) (T : SplitTailTest k q), HasSplitPartialTest k q a Φ T →
    ∀ (W : complexWhittakerModel Order ds (-a)) (g : H) (s : ℂ),
      let μ := complexSelfDualMeasure a
      let χ := characterWeight d (((Order + 2 : ℕ) : ℂ) / 2 + s - 1)
      let M (p : Outer k q) : ℂ :=
        (((complexNormalizedAbs (retainedMatrix k q p).val.det)⁻¹ : ℝ) : ℂ) ^ q *
          ∫ z, alternateBlockTailKernel k q a T W.val χ g p.1.1.1 (retainedMatrix k q p) z
            ∂entryHaar μ (q + 1)
      Integrable M (outerMeasure k q μ κ) ∧
      continuedValue (complexGeneralLinearHaar Size) μ d a Φ W.val
          (padGL (Nat.le_succ Size) (iSmall g)) s =
        (d.character ((-1 : ℂˣ) ^ Size) : ℂ) * P (iSmall g) (1 / 2) *
          (c : ℂ) * ∫ p, M p ∂outerMeasure k q μ κ

set_option maxHeartbeats 950000 in
theorem complexGapSplitPartialRestriction : ComplexGapSplitPartialRestrictionStatement k q := by
  intro hk a κ hκ hκinv
  let μ := complexSelfDualMeasure a
  let ν := complexGeneralLinearHaar Size
  let η := entryHaar μ (q + 1)
  let ρ := (rectangularMeasure μ k q).prod η
  let θ := outerMeasure k q μ κ
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace K := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : SigmaFinite κ := inferInstance
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : (rectangularMeasure μ k q).IsAddHaarMeasure := rectangularMeasure_isAddHaar μ _ _
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SigmaFinite ρ := inferInstanceAs (SigmaFinite ((rectangularMeasure μ k q).prod η))
  let : SigmaFinite θ := by unfold θ outerMeasure; infer_instance
  have hChart := (continuous_triangularRightChart k q).measurable
  obtain ⟨c, hc, hcν⟩ := complexGapTriangularChart k q hk μ κ hκ hκinv
  have hHaar : ν = (c : ℝ≥0∞) • ((θ.prod ρ).map (triangularRightChart k q)) := hcν
  refine ⟨c, hc, ?_⟩
  intro d ds Φ T hΦ W g s _ χ M
  let F := paddedRestrictionKernel μ d a Φ W.val (iSmall g) 1 s
  let O (p : Outer k q × (Tail × N)) := ordinaryBlockTailKernel k q T W.val χ
    g p.1.1.1.1 (retainedMatrix k q p.1) p.2
  have hO : F ∘ triangularRightChart k q = O :=
    funext (ordinaryKernel_eq k q a d ds Φ T hΦ W g s)
  obtain ⟨hF, hValue⟩ := complexGodementPaddedRestriction Order ds a ν
    (inferInstanceAs ν.IsHaarMeasure) (inferInstanceAs ν.IsMulRightInvariant) μ d Φ W (iSmall g) 1 s
  change Integrable F ν at hF
  have hMap : Integrable F ((θ.prod ρ).map (triangularRightChart k q)) := by
    rw [hHaar] at hF
    exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hF
  have hIntO : Integrable O (θ.prod ρ) :=
    hO ▸ (integrable_map_measure hMap.aestronglyMeasurable hChart.aemeasurable).mp hMap
  have hMarginal (p : Outer k q) : (∫ v, O (p, v) ∂ρ) = M p :=
    (complexGapTailExchange k q a T ds W χ g p.1.1.1 (retainedMatrix k q p)).2.2
  have hInt : (∫ x, F x ∂ν) = (c : ℂ) * ∫ p, M p ∂θ := by
    rw [hHaar, integral_smul_measure, integral_map hChart.aemeasurable hMap.aestronglyMeasurable,
      ENNReal.coe_toReal, Complex.real_smul]
    change (c : ℂ) * (∫ x, (F ∘ triangularRightChart k q) x ∂θ.prod ρ) = _
    rw [hO, integral_prod O hIntO]
    simp_rw [hMarginal]
  refine ⟨hIntO.integral_prod_left.congr (ae_of_all _ hMarginal), ?_⟩
  simpa only [mul_one, map_one, hInt, mul_assoc, F] using hValue

end Langlands.Global.RankinSelbergGlobal.ComplexGapSplitPartialRestriction
