import Langlands.Global.RankinSelberg.ComplexGapInverseTransposeTailBound
import Langlands.Global.RankinSelberg.ComplexGapOrdinaryConvergence
import Langlands.Global.RankinSelberg.ComplexGapTriangularFourier

/-! # Joint convergence for the alternate complex tail -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateTailConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply
  upperEntryProductMeasure)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (ComplexQuotientMeasureData)
open ComplexGapInverseTransposeTailBound (inverseTailColumns complexGapInverseTransposeTailBound)
open ComplexGapLeadingSchwartz (matrixDecay)
open ComplexGapOrdinaryConvergence (firstTorusDecay integrable_firstTorusDecay)
open ComplexGapTailEndpoints (firstTailColumn)
open ComplexGapColumnFourier (measurePreserving_entryHaar_inv)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexLocalIwasawa (alphaQ)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexTwoBlockHaar (rightTail blockLog)
open RealConvergenceAnalysis (rootPos integrable_exp_neg_mul_sum_abs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "Z" => fun r t => Fin (r + 1 - (t + 1)) → ℝ
local notation "X" => fun t => Fin (t + 1) → ℂ
local notation "Coords" => fun r t => LeftUnipotentQuotient t ℂ ×
  (Z r t × (N (r + 1 - (t + 1)) × (X t × KU (r + 1))))

local instance gapAlternateGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapAlternateGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapAlternateNMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance gapAlternateNBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

/-- The product of the compatible quotient measure and the four tail chart measures. -/
def alternateTailProductMeasure (r t : ℕ) (D : ComplexQuotientMeasureData t)
    (μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1))) : Measure (Coords r t) :=
  D.measure.prod (volume.prod ((entryHaar μ (r + 1 - (t + 1))).prod ((rowMeasure μ (t + 1)).prod κ)))

private def firstRectangle {r t : ℕ} (x : X t) : Mat (t + 1) (r + 1 - (t + 1)) :=
  fun i j => if j.val = 0 then x i else 0

/-- The alternate tail envelope with the leading logarithms taken on the quotient. -/
def alternateTailEnvelope {r t : ℕ} (h : t < r) (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ))
    (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ)) (A B T : ℝ) (J l m : ℕ) (v : Coords r t) : ℝ :=
  let hk := Nat.succ_pos t
  let hkn := Nat.succ_lt_succ h
  let y := alphaQ v.1
  let z := v.2.1
  let g := rightTail hk hkn (logTorus (-z) * v.2.2.1.val) (firstRectangle v.2.2.2.1) v.2.2.2.2
  let u := firstTailColumn hk hkn g
  let M := inverseTailColumns hkn g
  ‖Φ u * Ξ M‖ * (1 + ‖u‖) ^ l * (1 + ‖M‖) ^ m *
    Real.exp (A * (∑ i, |y i|) + B * (∑ j, |z j|) + T * (∑ i, y i) -
      (J : ℝ) * rootPos (blockLog hkn y z))

private def decay {E : Type*} [NormedAddCommGroup E] (p : ℕ) (x : E) : ℝ :=
  ((1 + ‖x‖) ^ p)⁻¹

private theorem integrable_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℕ} (hp : Module.finrank ℝ E < p) :
    Integrable (decay p) μ := by
  refine (integrable_one_add_norm (μ := μ) (r := (p : ℝ)) (by exact_mod_cast hp)).congr ?_
  exact ae_of_all _ fun x => by
    simp only [decay, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast]

private theorem integrable_inverseTailDecay (μ : AdditiveHaarMeasure ℂ) (d : ℕ) (hd : 0 < d) :
    ∃ p : ℕ, Integrable (fun u : N d => matrixDecay p u.val⁻¹.val) (entryHaar μ d) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let p := Module.finrank ℝ (UpperEntryPair (q + 1) → ℂ) + 1
  let e := (upperEntryCoordinates (K := ℂ) (q + 1)).toMeasurableEquiv
  let ν := entryHaar μ (q + 1)
  let ρ := upperEntryProductMeasure μ (q + 1)
  have he : MeasurePreserving e.symm ρ ν := ⟨e.symm.measurable, rfl⟩
  have hDecay : Integrable (decay p) ρ := integrable_decay ρ (Nat.lt_succ_self _)
  have he' : MeasurePreserving e ν ρ := he.symm
  have hBase := (he'.integrable_comp_emb e.measurableEmbedding).mpr hDecay
  have hMeas : Measurable (fun u : N (q + 1) => matrixDecay p u.val.val) := by
    have hVal : Measurable (fun u : N (q + 1) => u.val.val) :=
      (Units.continuous_val.comp continuous_subtype_val).measurable
    exact ((measurable_const.add hVal.norm).pow_const p).inv
  have hI : Integrable (fun u : N (q + 1) => matrixDecay p u.val.val) ν := by
    refine hBase.mono' hMeas.aestronglyMeasurable (ae_of_all _ fun u => ?_)
    have hEntry : ‖e u‖ ≤ ‖u.val.val‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => by
        change ‖upperEntryCoordinates (q + 1) u j‖ ≤ _
        rw [upperEntryCoordinates_apply]
        exact Matrix.norm_entry_le_entrywise_sup_norm u.val.val (i := j.val.1) (j := j.val.2)
    have hPos : 0 ≤ matrixDecay p u.val.val := by unfold matrixDecay; positivity
    rw [Real.norm_of_nonneg hPos]
    change ((1 + ‖u.val.val‖) ^ p)⁻¹ ≤ ((1 + ‖e u‖) ^ p)⁻¹
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by gcongr)
  let inv := MeasurableEquiv.inv (N (q + 1))
  have hi : MeasurePreserving inv ν ν := measurePreserving_entryHaar_inv q μ
  exact ⟨p, (hi.integrable_comp_emb inv.measurableEmbedding).mpr hI⟩

/-- All measurable kernels dominated by the alternate tail envelope for a suitable root
order are integrable on the quotient and the retained tail coordinates. -/
def ComplexGapAlternateTailConvergenceStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t)
    (μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1))), κ.IsHaarMeasure →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (A B T : ℝ), 0 ≤ B → A + L + 1 ≤ T →
    ∀ (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ)) (l m : ℕ),
      ∃ J : ℕ, ∀ (C : ℝ), 0 ≤ C → ∀ (F : Coords r t → ℂ),
        let ν := alternateTailProductMeasure r t D μ κ
        AEStronglyMeasurable F ν →
        (∀ v, ‖F v‖ ≤ C * alternateTailEnvelope h Φ Ξ A B T J l m v) → Integrable F ν

set_option maxHeartbeats 700000 in
theorem complexGapAlternateTailConvergence : ComplexGapAlternateTailConvergenceStatement := by
  intro r t h D μ κ hκ
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace (KU (r + 1)) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let d := r + 1 - (t + 1)
  let ρ := entryHaar μ d
  let ν := rowMeasure μ (t + 1)
  let : SigmaFinite ρ := entryHaar_sigmaFinite μ d
  let : SigmaFinite ν := inferInstanceAs (SigmaFinite (rowMeasure μ (t + 1)))
  let : SigmaFinite κ := inferInstance
  let : SigmaFinite (ν.prod κ) := inferInstance
  let : SigmaFinite (ρ.prod (ν.prod κ)) := inferInstance
  let : SigmaFinite ((volume : Measure (Z r t)).prod (ρ.prod (ν.prod κ))) := inferInstance
  let p := Module.finrank ℝ (X t) + 1
  have hX : Integrable (decay p) ν := integrable_decay ν (Nat.lt_succ_self _)
  obtain ⟨q, hU⟩ := integrable_inverseTailDecay μ d (Nat.sub_pos_of_lt (Nat.succ_lt_succ h))
  obtain ⟨c, L, hL⟩ := complexIwasawaToralMeasure t D
  have hQ := integrable_firstTorusDecay D c L hL
  have hZ : Integrable (fun z : Z r t => Real.exp (-∑ j, |z j|)) volume := by
    simpa only [neg_one_mul] using
      integrable_exp_neg_mul_sum_abs (n := d) (show (0 : ℝ) < 1 from one_pos)
  have hκ₁ : Integrable (fun _ : KU (r + 1) => (1 : ℝ)) κ := integrable_const 1
  refine ⟨‖L‖, norm_nonneg _, fun A B T hB hT Φ Ξ l m => ?_⟩
  obtain ⟨J, C', hC', hBound⟩ := complexGapInverseTransposeTailBound r (t + 1) (Nat.succ_pos t)
    (Nat.succ_lt_succ h) (A + ‖L‖) B T 1 hB hT Φ Ξ l m p q
  refine ⟨J, fun C hC F hF hFbound => ?_⟩
  have hProd := (hQ.mul_prod (hZ.mul_prod (hU.mul_prod (hX.mul_prod hκ₁)))).const_mul (C * C')
  change Integrable F (alternateTailProductMeasure r t D μ κ)
  refine hProd.mono' hF (ae_of_all _ fun v => ?_)
  let y := alphaQ v.1
  let z := v.2.1
  let u := v.2.2.1
  let x := v.2.2.2.1
  let Y := ∑ i, |y i|
  let S := ∑ j, |z j|
  have hEnvelope :
      alternateTailEnvelope h Φ Ξ A B T J l m v =
        Real.exp (-‖L‖ * Y) * alternateTailEnvelope h Φ Ξ (A + ‖L‖) B T J l m v := by
    unfold alternateTailEnvelope
    dsimp only
    rw [show A * Y + B * S + T * (∑ i, y i) - (J : ℝ) * rootPos (blockLog (Nat.succ_lt_succ h) y z) =
      -‖L‖ * Y + ((A + ‖L‖) * Y + B * S + T * (∑ i, y i) -
        (J : ℝ) * rootPos (blockLog (Nat.succ_lt_succ h) y z)) by ring, Real.exp_add]
    ring
  have hDecayBound := hBound y z u (firstRectangle (r := r) x) v.2.2.2.2
  change alternateTailEnvelope h Φ Ξ (A + ‖L‖) B T J l m v ≤
    C' * Real.exp (-Y - 1 * S) *
      ((1 + ‖fun i => firstRectangle (r := r) x i ⟨0, Nat.sub_pos_of_lt (Nat.succ_lt_succ h)⟩‖) ^ p)⁻¹ *
      matrixDecay q u.val⁻¹.val at hDecayBound
  simp only [firstRectangle, one_mul] at hDecayBound
  change _ ≤ C' * Real.exp (-Y - S) * decay p x * matrixDecay q u.val⁻¹.val at hDecayBound
  rw [sub_eq_add_neg, Real.exp_add] at hDecayBound
  calc
    ‖F v‖ ≤ C * alternateTailEnvelope _ Φ Ξ A B T J l m v := hFbound v
    _ = C * (Real.exp (-‖L‖ * Y) * alternateTailEnvelope _ Φ Ξ (A + ‖L‖) B T J l m v) := by
      rw [hEnvelope]
    _ ≤ C * (Real.exp (-‖L‖ * Y) *
        (C' * (Real.exp (-Y) * Real.exp (-S)) * decay p x * matrixDecay q u.val⁻¹.val)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDecayBound (Real.exp_nonneg _)) hC
    _ = _ := by
      dsimp only [firstTorusDecay]
      rw [show -(‖L‖ + 1) * Y = -‖L‖ * Y + (-Y) by ring, Real.exp_add, mul_one]
      ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateTailConvergence
