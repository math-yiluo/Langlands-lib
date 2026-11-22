import Langlands.Global.RankinSelberg.ComplexGapAlternateMajorant

/-! # Absolute convergence for the split alternate complex chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSplitNormConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (ComplexQuotientMeasureData)
open ComplexGapAlternateMajorant (alternateGapNorm complexGapAlternateMajorant)
open ComplexGapInverseTransposeTailBound (inverseTailColumns)
open ComplexGapAlternateTailConvergence (alternateTailProductMeasure alternateTailEnvelope
  complexGapAlternateTailConvergence)
open ComplexGapLeadingSchwartz (matrixDecay weightedMatrixTail)
open ComplexGapTailEndpoints (firstTailColumn)
open ComplexLocalIwasawa (alphaQ continuous_alphaQ continuous_logTorus)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexTwoBlockHaar (rightTail diagonalBlocks upperRectangle continuous_diagonalBlocks
  continuous_upperRectangle blockLog)
open RealConvergenceAnalysis (rootPos)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "H" => complexMatrixHeight
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Tail" => fun r t => Q t × ((Fin (r + 1 - (t + 1)) → ℝ) ×
  (N (r + 1 - (t + 1)) × ((Fin (t + 1) → ℂ) × KU (r + 1))))
local notation "Lower" => fun r t => Mat (r + 1 - (t + 1)) (t + 1)
local notation "Chart" => fun r t => Tail r t × (G (t + 1) × Lower r t)

attribute [local instance] ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

local instance gapAlternateGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapAlternateGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapAlternateNMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance gapAlternateNBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

private theorem continuous_alternateTailEnvelope {r t : ℕ} (h : t < r)
    (φ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (A B T : ℝ) (J l m : ℕ) :
    Continuous (alternateTailEnvelope h φ Ξ A B T J l m) := by
  let n := r + 1
  let k := t + 1
  let d := n - k
  let hk : 0 < k := Nat.succ_pos t
  let hkn : k < n := Nat.succ_lt_succ h
  let y (p : Tail r t) := alphaQ p.1
  let z (p : Tail r t) := p.2.1
  let X (p : Tail r t) : Mat k d := fun i j => if j.val = 0 then p.2.2.2.1 i else 0
  let w (p : Tail r t) := logTorus (-(z p)) * p.2.2.1.val
  let g (p : Tail r t) := rightTail hk hkn (w p) (X p) p.2.2.2.2
  have hy : Continuous y := continuous_alphaQ.comp continuous_fst
  have hz : Continuous z := continuous_fst.comp continuous_snd
  have hX : Continuous X := by
    apply continuous_matrix
    intro i j
    unfold X
    by_cases hj : j.val = 0
    · simp [hj]
      exact (continuous_apply i).comp (continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)))
    · simp [hj]
      exact continuous_const
  have hw : Continuous w := (continuous_logTorus.comp hz.neg).mul
    (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hg : Continuous g := by
    unfold g rightTail
    exact ((continuous_subtype_val.comp
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))).mul
      ((continuous_diagonalBlocks hk hkn).comp (continuous_const.prodMk hw))).mul
      ((continuous_upperRectangle hk hkn).comp hX)
  have hFirst : Continuous (fun p => firstTailColumn hk hkn (g p)) := by
    apply continuous_pi
    intro i
    unfold firstTailColumn
    exact (Units.continuous_val.comp hg).matrix_elem _ _
  have hInv : Continuous (fun p => inverseTailColumns hkn (g p)) := by
    apply continuous_matrix
    intro i j
    unfold inverseTailColumns
    exact (Units.continuous_val.comp hg.inv).matrix_elem _ _
  have hBlock : Continuous (fun p => blockLog hkn (y p) (z p)) := by
    apply continuous_pi
    intro i
    change Continuous (fun p => Fin.append (y p) (z p) ((finCongr (Nat.add_sub_of_le hkn.le)).symm i))
    refine Fin.addCases (m := k) (n := d) (fun j => ?_) (fun j => ?_)
      ((finCongr (Nat.add_sub_of_le hkn.le)).symm i)
    · change Continuous (fun p : Tail r t => Fin.append (y p) (z p) (Fin.castAdd d j))
      rw [show (fun p : Tail r t => Fin.append (y p) (z p) (Fin.castAdd d j)) =
        (fun p => y p j) from funext fun p => Fin.append_left (y p) (z p) j]
      exact (continuous_apply j).comp hy
    · change Continuous (fun p : Tail r t => Fin.append (y p) (z p) (Fin.natAdd k j))
      rw [show (fun p : Tail r t => Fin.append (y p) (z p) (Fin.natAdd k j)) =
        (fun p => z p j) from funext fun p => Fin.append_right (y p) (z p) j]
      exact (continuous_apply j).comp hz
  have hRoot : Continuous (fun p => rootPos (blockLog hkn (y p) (z p))) := by
    unfold rootPos
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i.castSucc).comp hBlock).sub ((continuous_apply i.succ).comp hBlock)).max
        continuous_const
  have hY : Continuous (fun p => ∑ i, |y p i|) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hy).abs
  have hZ : Continuous (fun p => ∑ i, |z p i|) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hz).abs
  have hSum : Continuous (fun p => ∑ i, y p i) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp hy
  have hE := Real.continuous_exp.comp
    ((((hY.const_mul A).add (hZ.const_mul B)).add (hSum.const_mul T)).sub (hRoot.const_mul (J : ℝ)))
  exact ((((φ.continuous.comp hFirst).mul (Ξ.continuous.comp hInv)).norm.mul
    ((continuous_const.add hFirst.norm).pow l)).mul ((continuous_const.add hInv.norm).pow m)).mul hE

/-- The alternate chart product, with a lower-rectangle measure admitting a decay estimate. -/
def alternateGapProductMeasure (r t : ℕ) (D : ComplexQuotientMeasureData t)
    (μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1))) (νY : Measure (Lower r t)) :
    Measure (Chart r t) :=
  (alternateTailProductMeasure r t D μ κ).prod ((complexGeneralLinearHaar (t + 1)).prod νY)

/-- Kernels dominated by the split alternate norm product are absolutely integrable for
sufficiently large independent leading exponents. -/
def ComplexGapSplitNormConvergenceStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ)
    (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
    (L : G (r + 1) → G (r + 1)) (R : G (t + 1) → G (t + 1)),
    (∀ x, H (L x) ≤ H x) → (∀ x, H (R x) ≤ H x) →
    ∀ (D : ComplexQuotientMeasureData t) (μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1))),
    κ.IsHaarMeasure → ∀ (νY : Measure (Lower r t)) [SigmaFinite νY],
    (∃ l : ℕ, Integrable (matrixDecay l) νY) →
    ∃ σ τ : ℝ, ∀ (u s b : ℝ), σ ≤ u → τ ≤ s → 0 ≤ b →
    ∀ (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (φ : 𝓢(Fin (r + 1) → ℂ, ℂ))
      (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ)) (C : ℝ), 0 ≤ C → ∀ (F : Chart r t → ℂ),
      let ν := alternateGapProductMeasure r t D μ κ νY
      AEStronglyMeasurable F ν →
      (∀ p, ‖F p‖ ≤ C * alternateGapNorm h Φ φ Ξ W.val V.val L R u s b p.1 p.2.1 p.2.2) →
      Integrable F ν

set_option maxHeartbeats 950000 in
theorem complexGapSplitNormConvergence : ComplexGapSplitNormConvergenceStatement := by
  intro r t h ds es a W V L R hL hR D μ κ hκ νY _ hY
  obtain ⟨l, hl⟩ := hY
  obtain ⟨τ, A, M, _, hMajor⟩ := complexGapAlternateMajorant r t h ds es a W V L R hL hR
  obtain ⟨A₀, _, hTail⟩ := complexGapAlternateTailConvergence r t h D μ κ hκ
  let σ := (A + A₀ + 1) / 2
  refine ⟨σ, τ, fun u s b hu hs hb Φ φ Ξ C hC F hF hFbound => ?_⟩
  obtain ⟨j, m, B, hB, hj, hBound⟩ := hMajor u s b hs hb Φ φ Ξ l
  have hT : A + A₀ + 1 ≤ 2 * u := by dsimp only [σ] at hu; linarith
  obtain ⟨J, hJ⟩ := hTail A B (2 * u) hB hT φ Ξ m m
  obtain ⟨C', _, hC'⟩ := hBound J
  let E := alternateTailEnvelope h φ Ξ A B (2 * u) J m m
  have hEN (p : Tail r t) : ‖(E p : ℂ)‖ = E p := by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    unfold E alternateTailEnvelope
    positivity
  have hE : Integrable E (alternateTailProductMeasure r t D μ κ) := by
    have hc := continuous_alternateTailEnvelope h φ Ξ A B (2 * u) J m m
    have hI := hJ 1 zero_le_one (fun p => (E p : ℂ))
      (Complex.continuous_ofReal.comp hc).aestronglyMeasurable
      (fun p => by rw [hEN, one_mul])
    exact hI.norm.congr (ae_of_all _ hEN)
  let : SigmaFinite ((complexGeneralLinearHaar (t + 1)).prod νY) := inferInstance
  have hI := (hE.mul_prod (hj.mul_prod hl)).const_mul (C * C')
  change Integrable F (alternateGapProductMeasure r t D μ κ νY)
  refine hI.mono' hF (ae_of_all _ fun p => ?_)
  calc
    ‖F p‖ ≤ C * alternateGapNorm h Φ φ Ξ W.val V.val L R u s b p.1 p.2.1 p.2.2 := hFbound p
    _ ≤ C * (C' * weightedMatrixTail M j s p.2.1 * matrixDecay l p.2.2 * E p.1) :=
      mul_le_mul_of_nonneg_left (hC' p.1 p.2.1 p.2.2) hC
    _ = (C * C') * (E p.1 * (weightedMatrixTail M j s p.2.1 * matrixDecay l p.2.2)) := by ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapSplitNormConvergence
