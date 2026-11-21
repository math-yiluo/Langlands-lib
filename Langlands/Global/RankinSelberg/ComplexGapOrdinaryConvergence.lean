import Langlands.Global.RankinSelberg.ComplexGapOrdinaryMajorant
import Langlands.Global.RankinSelberg.ComplexGodementTwoBlockRestriction

/-! # Joint absolute convergence in the ordinary complex gap chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinaryConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs)
open ComplexGapLeadingSchwartz (matrixDecay weightedMatrixTail exists_integrable_weightedMatrixTail)
open ComplexGapOrdinaryMajorant (ordinaryGapNorm complexGapOrdinaryMajorant)
open ComplexLocalIwasawa (alpha alphaQ alphaQ_mk continuous_alphaQ)
open RealConvergenceAnalysis (lintegral_exp_neg_mul_sum_abs_lt_top)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "N" => fun t => Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ
local notation "X" => fun r t => Mat (t + 1) (r + 1 - (t + 1))
local notation "Y" => fun r t => Mat (r + 1 - (t + 1)) (t + 1)
local notation "H" => fun r t => G (t + 1) × G (r + 1 - (t + 1))
local notation "Tail" => fun r t => ((H r t) × X r t) × KU (r + 1)
local notation "Coords" => fun r t => Q t × (Y r t × Tail r t)
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

local instance gapOrdGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapOrdGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

local instance gapOrdGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
local instance gapOrdGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
local instance gapOrdQSigmaCompact (t : ℕ) : SigmaCompactSpace (Q t) := by
  let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let e := leftQuotient_isOpenQuotientMap (N t)
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr e.surjective]
  exact isSigmaCompact_range e.continuous

/-- The product before multiplying by the right-tail determinant density. -/
def ordinaryGapProductMeasure (r t : ℕ) (D : ComplexQuotientMeasureData t) (ν νY : AdditiveHaarMeasure ℂ)
    (κ : Measure (KU (r + 1))) : Measure (Coords r t) :=
  D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod
    ((((complexGeneralLinearHaar (t + 1)).prod (complexGeneralLinearHaar (r + 1 - (t + 1)))).prod
      (rectangularMeasure ν (t + 1) (r + 1 - (t + 1)))).prod κ))

private theorem integrable_rectangle_decay (ν : AdditiveHaarMeasure ℂ) (m n : ℕ)
    (p : ℕ) (hp : Module.finrank ℝ (Mat m n) < p) :
    Integrable (matrixDecay p : Mat m n → ℝ) (rectangularMeasure ν m n) := by
  let : (rectangularMeasure ν m n).IsAddHaarMeasure := rectangularMeasure_isAddHaar ν _ _
  refine (integrable_one_add_norm (μ := rectangularMeasure ν m n) (r := (p : ℝ)) (by exact_mod_cast hp)).congr ?_
  exact ae_of_all _ fun A => by
    simp only [matrixDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖A‖), Real.rpow_natCast]

private theorem exists_integrable_tail_decay (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, Integrable (fun g : G n => δ g ^ n * matrixDecay p g.val) (complexGeneralLinearHaar n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hs : ((r + 1 : ℕ) : ℝ) + (0 : ℕ) ≤ (r + 1 : ℕ) := by simp
  obtain ⟨p, hp⟩ := exists_integrable_weightedMatrixTail r 0 ((r + 1 : ℕ) : ℝ) hs
  refine ⟨p, ?_⟩
  unfold weightedMatrixTail at hp
  simpa only [pow_zero, one_mul, Real.rpow_natCast] using hp

private def firstTorusDecay {t : ℕ} (A : ℝ) (q : Q t) : ℝ :=
  Real.exp (-(A + 1) * ∑ i, |alphaQ q i|)

private theorem integrable_firstTorusDecay {t : ℕ} (D : ComplexQuotientMeasureData t)
    (c : ℝ≥0) (L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ)
    (hL : ∀ B : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂D.measure = (c : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) * B y) :
    Integrable (firstTorusDecay ‖L‖) D.measure := by
  let F := fun y : Fin (t + 1) → ℝ => Real.exp (-(‖L‖ + 1) * ∑ i, |y i|)
  have hlen : Continuous (fun y : Fin (t + 1) → ℝ => ∑ i, |y i|) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).abs
  have hF : Continuous F := Real.continuous_exp.comp (continuous_const.mul hlen)
  refine ⟨(hF.comp continuous_alphaQ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  change ∫⁻ q, ENNReal.ofReal ‖F (alphaQ q)‖ ∂D.measure < ⊤
  have he (q : Q t) : ‖F (alphaQ q)‖ = F (alphaQ q) := Real.norm_of_nonneg (Real.exp_nonneg _)
  simp_rw [he]
  let B := fun y => ENNReal.ofReal (F y)
  change ∫⁻ q, B (alphaQ q) ∂D.measure < ⊤
  rw [hL B (ENNReal.measurable_ofReal.comp hF.measurable)]
  apply ENNReal.mul_lt_top ENNReal.coe_lt_top
  calc
    _ ≤ ∫⁻ y : Fin (t + 1) → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ i, |y i|)) := by
      refine lintegral_mono fun y => ?_
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [B, F]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hy := RealEqualConvergence.linear_le L y
      linarith
    _ < ⊤ := lintegral_exp_neg_mul_sum_abs_lt_top one_pos

/-- The full split ordinary kernel has a joint absolute majorant for the actual compatible
quotient Haar, two group Haar measures, the two additive rectangle measures, and compact Haar.
The inequality premise permits replacement of the spectral powers by bounded radial weights. -/
def ComplexGapOrdinaryConvergenceStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ)
    (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
    (D : ComplexQuotientMeasureData t) (ν νY : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1))),
    κ.IsHaarMeasure → ∃ σ τ : ℝ, ∀ (u s b : ℝ), σ ≤ u → τ ≤ s →
    ∀ (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
      (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (C₀ : ℝ), 0 ≤ C₀ → ∀ (F : Coords r t → ℂ),
      let μ := ordinaryGapProductMeasure r t D ν νY κ
      AEStronglyMeasurable F μ →
      (∀ p, ‖F p‖ ≤ C₀ * ordinaryGapNorm h Φ Ξ Ψ W.val V.val u s b p.1.out
        p.2.2.1.1.1 p.2.2.1.1.2 p.2.2.1.2 p.2.1 p.2.2.2) → Integrable F μ

set_option maxHeartbeats 950000 in
theorem complexGapOrdinaryConvergence : ComplexGapOrdinaryConvergenceStatement := by
  intro r t h ds es a W V D ν νY κ hκ
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace (KU (r + 1)) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let ρX := rectangularMeasure ν (t + 1) (r + 1 - (t + 1))
  let ρY := rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)
  let : ρX.IsAddHaarMeasure := rectangularMeasure_isAddHaar ν _ _
  let : ρY.IsAddHaarMeasure := rectangularMeasure_isAddHaar νY _ _
  let μ₁ := complexGeneralLinearHaar (t + 1)
  let μ₂ := complexGeneralLinearHaar (r + 1 - (t + 1))
  let : SigmaFinite μ₁ := inferInstanceAs (SigmaFinite (complexGeneralLinearHaar (t + 1)))
  let : SigmaFinite μ₂ := inferInstanceAs (SigmaFinite (complexGeneralLinearHaar (r + 1 - (t + 1))))
  let : SigmaFinite ρX := inferInstance
  let : SigmaFinite ρY := inferInstance
  let : SigmaFinite κ := inferInstance
  let : SigmaFinite (μ₁.prod μ₂) := inferInstance
  let : SigmaFinite ((μ₁.prod μ₂).prod ρX) := inferInstance
  let : SigmaFinite (((μ₁.prod μ₂).prod ρX).prod κ) := inferInstance
  let : SigmaFinite (ρY.prod (((μ₁.prod μ₂).prod ρX).prod κ)) := inferInstance
  have hd : 0 < r + 1 - (t + 1) := Nat.sub_pos_of_lt (Nat.succ_lt_succ h)
  obtain ⟨c, L, hL⟩ := complexIwasawaToralMeasure t D
  have hIntQ := integrable_firstTorusDecay D c L hL
  obtain ⟨σ, τ, M, hMajor⟩ := complexGapOrdinaryMajorant r t h ds es a W V ‖L‖ (norm_nonneg _)
  obtain ⟨p, hp⟩ := exists_integrable_tail_decay _ hd
  let i := Module.finrank ℝ (X r t) + 1
  let l := Module.finrank ℝ (Y r t) + 1
  have hIntX : Integrable (matrixDecay i) ρX := integrable_rectangle_decay ν _ _ _ (Nat.lt_succ_self _)
  have hIntY : Integrable (matrixDecay l) ρY := integrable_rectangle_decay νY _ _ _ (Nat.lt_succ_self _)
  refine ⟨σ, τ, fun u s b hu hs Φ Ξ Ψ C₀ hC₀ F hF hFbound => ?_⟩
  obtain ⟨C, j, hC, hLead, hBound⟩ := hMajor u s b hu hs Φ Ξ Ψ p i l
  have hK : Integrable (fun _ : KU (r + 1) => (1 : ℝ)) κ := integrable_const 1
  change Integrable _ μ₁ at hLead
  change Integrable _ μ₂ at hp
  have hP := (hIntQ.mul_prod (hIntY.mul_prod (((hLead.mul_prod hp).mul_prod hIntX).mul_prod hK))).const_mul (C₀ * C)
  change Integrable F (ordinaryGapProductMeasure r t D ν νY κ)
  refine hP.mono' hF (ae_of_all _ fun v => ?_)
  let q := v.1
  have hNorm := hFbound v
  have hRep : alphaQ q = alpha q.out := by
    conv_lhs => rw [← Quotient.out_eq q]
    exact alphaQ_mk _
  have hMajor' := hBound q.out v.2.2.1.1.1 v.2.2.1.1.2 v.2.2.1.2 v.2.1 v.2.2.2
  have hFin := hNorm.trans (mul_le_mul_of_nonneg_left hMajor' hC₀)
  rw [← hRep] at hFin
  refine hFin.trans_eq ?_
  dsimp only [firstTorusDecay]
  rw [mul_one]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinaryConvergence
