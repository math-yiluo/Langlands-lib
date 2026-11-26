import Langlands.Global.RankinSelberg.RealGapOrdinaryConvergence
import Langlands.Global.RankinSelberg.RealGapSplitTestColumns
import Langlands.Global.RankinSelberg.RealGodementBlockUnfolding
import Langlands.Global.RankinSelberg.RealGapNormalizedWeighted
import Langlands.Global.RankinSelberg.RealWhittakerTranslatedIntegrals

/-! # Rapid determinant weights on the ordinary real gap kernel -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapOrdinaryWeighted

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant determinantContinuous)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs realUnequalIntegrand realFourierTransform)
open ArchimedeanMellinPair (RapidDecay)
open RealJacquet (detCharacter)
open RealGapAlternateWeighted (ordinaryKernel_mk left_translate leftCharacter_of_mem continuous_of_mem)
open RealGapOrdinaryConvergence (ordinaryGapProductMeasure realGapOrdinaryConvergence)
open RealGapOrdinaryMajorant (ordinaryGapNorm)
open RealGapSplitTestColumns (leadingColumns realGapSplitTestColumns)
open RealGodementLowerRectangle (lowerRectangle)
open RealGodementTwoBlockRestriction (rightTailProductMeasure)
open RealTwoBlockHaar (rightTail rightTailWeight diagonalBlocks tailColumns
  continuous_diagonalBlocks continuous_upperRectangle realNormalizedAbs_det_rightTail)
open RealUnequalFamily (HasLeftCharacter)
open RealUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs)
open RealWhittakerTranslatedIntegrals (weightedOrdinary)
open RealWhittakerTranslatedMellin (hasGaugeBound_of_mem_model)
open RealConvergenceAnalysis (norm_cexp_mul_ofReal)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "N" => fun t => Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "XR" => fun r t => Mat (t + 1) (r + 1 - (t + 1))
local notation "Y" => fun r t => Mat (r + 1 - (t + 1)) (t + 1)
local notation "Tail" => fun r t => (((G (t + 1) × G (r + 1 - (t + 1))) × XR r t) × KU (r + 1))
local notation "Par" => fun r t => Y r t × Tail r t
local notation "Coords" => fun r t => Q t × Par r t
local notation "Sq" => fun r => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Rows" => fun r => Fin (r + 1) → ℝ
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance gapWeightedGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapWeightedGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapWeightedGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapWeightedGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapWeightedUMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance gapWeightedUBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
local instance gapWeightedMatrixBorel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))
local instance gapWeightedMatrixSecondCountable (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
local instance gapWeightedKUSecondCountable (n : ℕ) : SecondCountableTopology (KU n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance gapWeightedKUOpens (n : ℕ) : OpensMeasurableSpace (KU n) :=
  Subtype.opensMeasurableSpace (fun g : G n => g ∈ unitaryCompact ℝ n)
local instance gapWeightedQSecondCountable (t : ℕ) : SecondCountableTopology (Q t) :=
  TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (N t)).isOpenMap
local instance gapWeightedQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapWeightedQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

private def tailOn {r t : ℕ} (h : t < r) (p : Par r t) : G (r + 1) :=
  rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) p.2.1.1.2 p.2.1.2 p.2.2

set_option maxHeartbeats 1000000 in
private theorem continuous_tailOn {r t : ℕ} (h : t < r) : Continuous (tailOn h) := by
  let hk := Nat.succ_pos t
  let he := Nat.succ_lt_succ h
  have h₀ : Continuous (fun p : Par r t => p.2.1.1) :=
    continuous_fst.comp (continuous_fst.comp continuous_snd)
  have hX : Continuous (fun p : Par r t => p.2.1.2) := continuous_snd.comp (continuous_fst.comp continuous_snd)
  have h₁ : Continuous (fun p : Par r t => p.2.2.val) := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have h₂ : Continuous (fun p : Par r t => diagonalBlocks hk he 1 p.2.1.1.2) :=
    (continuous_diagonalBlocks hk he).comp (continuous_const.prodMk (continuous_snd.comp h₀))
  unfold tailOn rightTail
  exact (h₁.mul h₂).mul ((continuous_upperRectangle hk he).comp hX)

private theorem continuous_lowerRectangle {r t : ℕ} (h : t < r) : Continuous (lowerRectangle h) := by
  unfold lowerRectangle
  exact (Langlands.GeneralLinear.reindexContinuous (R := ℝ)
    (finCongr (Nat.add_sub_of_le (Nat.succ_le_succ h.le)))).continuous.comp
    (Langlands.GeneralLinear.continuous_lowerBlockPair.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)))

/-- The real determinant power is continuous on the general linear group. -/
theorem continuous_detPower {n : ℕ} (s : ℂ) : Continuous (fun g : G n => P g s) := by
  have hδ : Continuous (fun g : G n => δ g) := Units.continuous_val.matrix_det.abs
  have hlog := hδ.log fun g => abs_ne_zero.mpr g.det_ne_zero
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

/-- A real character of the determinant is continuous on the general linear group. -/
theorem continuous_detCharacter (c : RealCharacterData) {n : ℕ} :
    Continuous (fun g : G n => detCharacter c.character.toMonoidHom g) :=
  Units.continuous_val.comp (c.character.continuous.comp determinantContinuous.continuous)

private theorem continuous_translated_product {r t : ℕ} (h : t < r) {ds es : List RealBlock}
    {a : ℝˣ} {W : G (r + 1) → ℂ} {V : G (t + 1) → ℂ} (hW : W ∈ realUniformWhittakerModel r ds (-a))
    (hV : V ∈ realUniformWhittakerModel t es (-(-a))) :
    Continuous (fun p : Coords r t => realUnequalIntegrand h
      (ρ (tailOn h p.2)⁻¹ W) (ρ p.2.2.1.1.1 V) 0 p.1) := by
  apply ((leftQuotient_isOpenQuotientMap (N t)).prodMap
    (IsOpenQuotientMap.id (X := Par r t))).isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : G (t + 1) × Par r t => realUnequalIntegrand h
    (ρ (tailOn h p.2)⁻¹ W) (ρ p.2.2.1.1.1 V) 0 (Quotient.mk _ p.1))
  simp_rw [ordinaryKernel_mk h (left_translate (leftCharacter_of_mem hW) _)
    (left_translate (leftCharacter_of_mem hV) _)]
  have hg : Continuous (fun p : G (t + 1) × Par r t =>
      padGL (Nat.succ_le_succ h.le) p.1 * (tailOn h p.2)⁻¹) :=
    ((UnequalAnalytic.continuous_padGL (Nat.succ_le_succ h.le)).comp continuous_fst).mul
      ((continuous_tailOn h).comp continuous_snd).inv
  exact (((continuous_of_mem hW).comp hg).mul ((continuous_of_mem hV).comp (by fun_prop))).mul
    ((continuous_detPower _).comp continuous_fst)

/-- The ordinary block kernel after the quotient change of variables, with independent
rapid radial weights on the quotient argument and the leading group variable. -/
def weightedBlockKernel {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Sq r → ℂ) (f : Rows r → ℂ) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Coords r t) : ℂ :=
  let z := p.2.2.1.1.1
  let B := tailOn h p.2
  let A := diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) z 1
  F (B * A * lowerRectangle h p.2.1).val * realFourierTransform a f (Langlands.RankinSelberg.lastRow B⁻¹) *
    (detCharacter c.character.toMonoidHom B * P B ((r : ℂ) / 2)) *
    ((detCharacter c.character.toMonoidHom z * P z ((r : ℂ) / 2)) * f₂ (δ z)) *
    weightedOrdinary h (ρ B⁻¹ W) (ρ z V) f₁ p.1

/-- Splitting the square test into its leading and trailing columns, together with a Schwartz
function for the transformed last factor, gives the three Schwartz factors of the ordinary
convergence estimate. -/
def HasSplitPartialTest {r t : ℕ} (h : t < r) (a : ℝˣ) (F : Sq r → ℂ) (f : Rows r → ℂ)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Rows r, ℂ)) : Prop :=
  (∀ C : G (r + 1), F C.val = Φ₀ (leadingColumns (Nat.succ_lt_succ h) C) *
    Ξ (tailColumns (Nat.succ_lt_succ h) C)) ∧ ∀ v, realFourierTransform a f v = Ψ v

private def tailDensity {r t : ℕ} (p : Coords r t) : ℝ≥0 :=
  rightTailWeight (k := t + 1) p.2.2.1.1.2

private theorem measurable_tailDensity {r t : ℕ} : Measurable (tailDensity (r := r) (t := t)) := by
  unfold tailDensity rightTailWeight
  exact ((continuous_nnnorm.comp Units.continuous_val.matrix_det).pow _).measurable.inv.comp
    (by fun_prop)

private theorem tailDensity_eq {r t : ℕ} (p : Coords r t) :
    (tailDensity p : ℝ) = δ p.2.2.1.1.2 ^ (-((t + 1 : ℕ) : ℝ)) := by
  let q := δ p.2.2.1.1.2
  have hq : 0 ≤ q := abs_nonneg _
  change ((‖(p.2.2.1.1.2).val.det‖₊ ^ (t + 1))⁻¹ : ℝ≥0) = q ^ (-((t + 1 : ℕ) : ℝ))
  rw [Real.rpow_neg hq, Real.rpow_natCast, NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs]
  rfl

private theorem weighted_measure_eq {r t : ℕ} (D : RealQuotientMeasureData t) (ν νY : AdditiveHaarMeasure ℝ)
    (μ₁ : Measure (G (t + 1))) (μ₂ : Measure (G (r + 1 - (t + 1)))) (κ : Measure (KU (r + 1)))
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [κ.IsHaarMeasure] :
    D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod
      (rightTailProductMeasure (r + 1) (t + 1) ν μ₁ μ₂ κ)) =
    (ordinaryGapProductMeasure r t D ν νY μ₁ μ₂ κ).withDensity (fun p => (tailDensity p : ℝ≥0∞)) := by
  let mTail := (((μ₁.prod μ₂).prod (rectangularMeasure ν (t + 1) (r + 1 - (t + 1)))).prod κ)
  let mY := rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)
  let θ := fun p : Tail r t => ((rightTailWeight (k := t + 1) p.1.1.2 : ℝ≥0) : ℝ≥0∞)
  let : (rectangularMeasure ν (t + 1) (r + 1 - (t + 1))).IsAddHaarMeasure := rectangularMeasure_isAddHaar ν _ _
  let : mY.IsAddHaarMeasure := rectangularMeasure_isAddHaar νY _ _
  let : SigmaFinite mTail := inferInstance
  let : SigmaFinite mY := inferInstance
  let : SigmaFinite (mY.prod mTail) := inferInstance
  have hθ : Measurable θ := by
    unfold θ rightTailWeight
    exact (((continuous_nnnorm.comp Units.continuous_val.matrix_det).pow (t + 1)).measurable.inv.coe_nnreal_ennreal).comp
      (by fun_prop)
  have hθ' : Measurable (fun p : Par r t => θ p.2) := hθ.comp measurable_snd
  change D.measure.prod (mY.prod (mTail.withDensity θ)) = (D.measure.prod (mY.prod mTail)).withDensity _
  rw [prod_withDensity_right hθ, prod_withDensity_right hθ']
  rfl

/-- The norm of the real determinant power is the real power of the absolute determinant. -/
theorem norm_detPower {n : ℕ} (g : G n) (s : ℂ) : ‖P g s‖ = δ g ^ s.re := by
  dsimp only
  have hp : 0 < δ g := abs_pos.mpr g.det_ne_zero
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Real.rpow_def_of_pos hp, mul_comm]

/-- The norm of a real character of the determinant is the power of the absolute determinant
at the real part of its exponent. -/
theorem norm_detCharacter (c : RealCharacterData) {n : ℕ} (g : G n) :
    ‖detCharacter c.character.toMonoidHom g‖ = δ g ^ c.exponent.re := by
  have hg : g.val.det ≠ 0 := (determinant g).ne_zero
  change ‖((c.character (determinant g) : ℂˣ) : ℂ)‖ = |g.val.det| ^ c.exponent.re
  rw [c.character_eq]
  have hd : ((determinant g : ℝˣ) : ℝ) = g.val.det := rfl
  rw [hd, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs,
    div_self (abs_ne_zero.mpr hg), one_pow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hg)]

private theorem continuous_leadingColumns {n k : ℕ} (hkn : k < n) :
    Continuous (fun g : G n => leadingColumns hkn g) :=
  continuous_pi fun i => continuous_pi fun _ => (Langlands.GeneralLinear.entry (R := ℝ) i _).continuous

private theorem continuous_tailColumns {n k : ℕ} (hkn : k < n) :
    Continuous (fun g : G n => tailColumns hkn g) :=
  continuous_pi fun i => continuous_pi fun _ => (Langlands.GeneralLinear.entry (R := ℝ) i _).continuous

set_option maxHeartbeats 1000000 in
private theorem measurable_weightedBlockKernel {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Sq r → ℂ) (f : Rows r → ℂ)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Rows r, ℂ)) (hΦ : HasSplitPartialTest h a F f Φ₀ Ξ Ψ)
    {ds es : List RealBlock} {W : G (r + 1) → ℂ} {V : G (t + 1) → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds (-a)) (hV : V ∈ realUniformWhittakerModel t es (-(-a)))
    (f₁ f₂ : ℝ → ℂ) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    Measurable (weightedBlockKernel h c a F f W V f₁ f₂) := by
  let he := Nat.succ_lt_succ h
  let B := fun p : Coords r t => tailOn h p.2
  let z := fun p : Coords r t => p.2.2.1.1.1
  let A := fun p : Coords r t => diagonalBlocks (Nat.succ_pos t) he (z p) 1
  let C := fun p : Coords r t => B p * A p * lowerRectangle h p.2.1
  have hB : Continuous B := (continuous_tailOn h).comp continuous_snd
  have hz : Continuous z := by fun_prop
  have hA : Continuous A := (continuous_diagonalBlocks (Nat.succ_pos t) he).comp
    (hz.prodMk continuous_const)
  have hy : Continuous (fun p : Coords r t => lowerRectangle h p.2.1) :=
    (continuous_lowerRectangle h).comp (continuous_fst.comp continuous_snd)
  have hC : Continuous C := (hB.mul hA).mul hy
  have hRow : Continuous (fun p : Coords r t => Langlands.RankinSelberg.lastRow (B p)⁻¹) :=
    continuous_pi fun j => (Langlands.GeneralLinear.entry (R := ℝ) (Fin.last r) j).continuous.comp hB.inv
  have hδz : Continuous (fun p : Coords r t => δ (z p)) := (Units.continuous_val.comp hz).matrix_det.abs
  have hK : weightedBlockKernel h c a F f W V f₁ f₂ = fun p =>
      Φ₀ (leadingColumns he (C p)) * Ξ (tailColumns he (C p)) *
        Ψ (Langlands.RankinSelberg.lastRow (B p)⁻¹) *
        (detCharacter c.character.toMonoidHom (B p) * P (B p) ((r : ℂ) / 2)) *
        ((detCharacter c.character.toMonoidHom (z p) * P (z p) ((r : ℂ) / 2)) * f₂ (δ (z p))) *
        (realUnequalIntegrand h (ρ (B p)⁻¹ W) (ρ (z p) V) 0 p.1 * f₁ (quotientDetAbs p.1)) := by
    funext p
    dsimp only [weightedBlockKernel, weightedOrdinary]
    rw [hΦ.1, hΦ.2]
  rw [hK]
  have h₁ := ((Φ₀.continuous.comp ((continuous_leadingColumns he).comp hC)).mul
    (Ξ.continuous.comp ((continuous_tailColumns he).comp hC))).mul (Ψ.continuous.comp hRow)
  have h₂ := ((continuous_detCharacter c).comp hB).mul ((continuous_detPower ((r : ℂ) / 2)).comp hB)
  have h₃ := ((continuous_detCharacter c).comp hz).mul ((continuous_detPower ((r : ℂ) / 2)).comp hz)
  have h₄ := continuous_translated_product h hW hV
  exact ((h₁.mul h₂).measurable.mul (h₃.measurable.mul (hf₂.comp hδz.measurable))).mul
    (h₄.measurable.mul (hf₁.comp (continuous_quotientDetAbs.measurable.comp measurable_fst)))

set_option maxHeartbeats 1000000 in
private theorem norm_weightedBlockKernel_le {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Sq r → ℂ) (f : Rows r → ℂ)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Rows r, ℂ)) (hΦ : HasSplitPartialTest h a F f Φ₀ Ξ Ψ)
    (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (f₁ f₂ : ℝ → ℂ)
    (u v C₁ C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hf₁ : ∀ x : ℝ, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ (u + ((r - t : ℕ) : ℝ) / 2))
    (hf₂ : ∀ x : ℝ, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ (v - (c.exponent.re + (r : ℝ) / 2)))
    (p : Coords r t) :
    ‖weightedBlockKernel h c a F f W V f₁ f₂ p‖ ≤
      (C₁ * C₂) * ordinaryGapNorm h Φ₀ Ξ Ψ W V u v (c.exponent.re + (r : ℝ) / 2)
        p.1.out p.2.2.1.1.1 p.2.2.1.1.2 p.2.2.1.2 p.2.1 p.2.2.2 := by
  let g := p.1.out
  let z := p.2.2.1.1.1
  let w := p.2.2.1.1.2
  let B := tailOn h p.2
  let k := Nat.succ_pos t
  let l := Nat.succ_lt_succ h
  let A := diagonalBlocks k l z 1
  let C := B * A * lowerRectangle h p.2.1
  let β := c.exponent.re + (r : ℝ) / 2
  let ω := ((r - t : ℕ) : ℝ) / 2
  have hg : 0 < δ g := abs_pos.mpr g.det_ne_zero
  have hz : 0 < δ z := abs_pos.mpr z.det_ne_zero
  have hw : 0 < δ w := abs_pos.mpr w.det_ne_zero
  obtain ⟨hL, hT⟩ := realGapSplitTestColumns r t h B z p.2.1
  have hTest := hΦ.1 C
  change F C.val = Φ₀ (leadingColumns l C) * Ξ (tailColumns l C) at hTest
  rw [hL, hT] at hTest
  have hχ (x : G (r + 1)) (hx : δ x = δ w) :
      ‖detCharacter c.character.toMonoidHom x * P x ((r : ℂ) / 2)‖ = δ w ^ β := by
    rw [norm_mul, norm_detCharacter, norm_detPower, hx]
    have hre : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by simp
    rw [hre, ← Real.rpow_add hw]
  have hBw : δ B = δ w := realNormalizedAbs_det_rightTail k l w p.2.2.1.2 p.2.2.2
  have hχz : ‖(detCharacter c.character.toMonoidHom z * P z ((r : ℂ) / 2)) * f₂ (δ z)‖ ≤
      C₂ * δ z ^ v := by
    rw [norm_mul, norm_mul, norm_detCharacter, norm_detPower]
    have hre : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by simp
    rw [hre, ← Real.rpow_add hz]
    calc
      _ ≤ δ z ^ β * (C₂ * δ z ^ (v - β)) :=
        mul_le_mul_of_nonneg_left (hf₂ _ hz) (Real.rpow_nonneg hz.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hz]; congr 2; ring
  have hPow : ‖P g (0 - ((r - t : ℕ) : ℂ) / 2)‖ = δ g ^ (-ω) := by
    rw [norm_detPower]
    have he : (0 : ℂ) - ((r - t : ℕ) : ℂ) / 2 = ((-ω : ℝ) : ℂ) := by
      dsimp only [ω]
      push_cast
      ring
    rw [he, Complex.ofReal_re]
  have hOrd : ‖weightedOrdinary h (ρ B⁻¹ W) (ρ z V) f₁ p.1‖ ≤
      ‖W (padGL l.le g * B⁻¹)‖ * ‖V (g * z)‖ * (C₁ * δ g ^ u) := by
    unfold weightedOrdinary realUnequalIntegrand ArchimedeanLocal.unequalIntegrand
      ArchimedeanLocal.translateFunction
    simp only [norm_mul]
    change ‖W (padGL l.le g * B⁻¹)‖ * ‖V (g * z)‖ * ‖P g (0 - ((r - t : ℕ) : ℂ) / 2)‖ *
      ‖f₁ (δ g)‖ ≤ _
    rw [hPow, mul_assoc (‖W (padGL l.le g * B⁻¹)‖ * ‖V (g * z)‖)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc
      _ ≤ δ g ^ (-ω) * (C₁ * δ g ^ (u + ω)) :=
        mul_le_mul_of_nonneg_left (hf₁ _ hg) (Real.rpow_nonneg hg.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hg]; congr 2; ring
  unfold weightedBlockKernel
  dsimp only
  change ‖F C.val * realFourierTransform a f (Langlands.RankinSelberg.lastRow B⁻¹) *
      (detCharacter c.character.toMonoidHom B * P B ((r : ℂ) / 2)) *
      ((detCharacter c.character.toMonoidHom z * P z ((r : ℂ) / 2)) * f₂ (δ z)) *
      weightedOrdinary h (ρ B⁻¹ W) (ρ z V) f₁ p.1‖ ≤ _
  have hrow : Langlands.RankinSelberg.lastRow B⁻¹ = B⁻¹.val (Fin.last r) := rfl
  rw [hTest, hΦ.2, hrow, norm_mul, norm_mul, norm_mul, hχ B hBw, norm_mul]
  have hβ := Real.rpow_nonneg hw.le β
  have hv := Real.rpow_nonneg hz.le v
  refine (mul_le_mul (mul_le_mul_of_nonneg_left hχz (by positivity)) hOrd (norm_nonneg _)
    (by positivity)).trans_eq ?_
  show _ = (C₁ * C₂) * (‖Φ₀ (B.val * RealGapOrdinaryMajorant.leadingInput _ z.val p.2.1)‖ *
    ‖Ξ (tailColumns l B) * Ψ (B⁻¹.val (Fin.last r))‖ * ‖W (padGL l.le g * B⁻¹)‖ * ‖V (g * z)‖ *
    δ g ^ u * δ z ^ v * δ w ^ β)
  rw [norm_mul (Φ₀ _), norm_mul (Ξ _)]
  ring

/-- The two rapid radial weights before normalization of the retained determinant, written
in the right-tail chart after the quotient shear. -/
def coupledWeightedBlockKernel {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Sq r → ℂ) (f : Rows r → ℂ) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Coords r t) : ℂ :=
  let b := δ (tailOn h p.2)
  weightedBlockKernel h c a F f W V (fun x => f₁ (x * b⁻¹))
    (fun x => f₂ (x * b) * (x : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2))) p

set_option maxHeartbeats 1000000 in
private theorem measurable_coupledWeightedBlockKernel {r t : ℕ} (h : t < r) (c : RealCharacterData)
    (a : ℝˣ) (F : Sq r → ℂ) (f : Rows r → ℂ)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Rows r, ℂ)) (hΦ : HasSplitPartialTest h a F f Φ₀ Ξ Ψ)
    {ds es : List RealBlock} {W : G (r + 1) → ℂ} {V : G (t + 1) → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds (-a)) (hV : V ∈ realUniformWhittakerModel t es (-(-a)))
    (f₁ f₂ : ℝ → ℂ) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    Measurable (coupledWeightedBlockKernel h c a F f W V f₁ f₂) := by
  let K := weightedBlockKernel h c a F f W V (fun _ => 1) (fun _ => 1)
  let b (p : Coords r t) := δ (tailOn h p.2)
  let z (p : Coords r t) := δ p.2.2.1.1.1
  let x (p : Coords r t) := quotientDetAbs p.1
  have hB : Measurable b :=
    ((Units.continuous_val.comp (continuous_tailOn h)).matrix_det.abs).measurable.comp measurable_snd
  have hz : Measurable z := by
    have : Continuous z := (Units.continuous_val.comp (by fun_prop :
      Continuous (fun p : Coords r t => p.2.2.1.1.1))).matrix_det.abs
    exact this.measurable
  have hx : Measurable x := continuous_quotientDetAbs.measurable.comp measurable_fst
  have hp : Measurable (fun p => (z p : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2))) :=
    (Complex.measurable_ofReal.comp hz).pow_const _
  have hK : Measurable K := measurable_weightedBlockKernel h c a F f Φ₀ Ξ Ψ hΦ hW hV _ _
    measurable_const measurable_const
  convert ((hK.mul (hf₁.comp (hx.mul hB.inv))).mul (hf₂.comp (hz.mul hB))).mul hp using 1
  funext p
  change _ = K p * f₁ (x p * (b p)⁻¹) * f₂ (z p * b p) * (z p : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2))
  unfold coupledWeightedBlockKernel K weightedBlockKernel weightedOrdinary
  dsimp only [x, z, b]
  ring

set_option maxHeartbeats 1500000 in
/-- The coupled right-tail estimate accepts independently chosen sufficiently large powers. -/
theorem realGapCoupledPowerBounds (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t)
    (ν νY : AdditiveHaarMeasure ℝ) (μ₁ : Measure (G (t + 1))) (μ₂ : Measure (G (r + 1 - (t + 1))))
    (κ : Measure (KU (r + 1))) [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [κ.IsHaarMeasure]
    (ds es : List RealBlock) (a : ℝˣ) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (hW : W ∈ realUniformWhittakerModel r ds (-a)) (hV : V ∈ realUniformWhittakerModel t es a)
    (c : RealCharacterData) (F : Sq r → ℂ) (f : Rows r → ℂ)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Rows r, ℂ)) (hΦ : HasSplitPartialTest h a F f Φ₀ Ξ Ψ) :
    ∃ α₀ γ₀ : ℝ, ∀ (f₁ f₂ : ℝ → ℂ) (α γ C₁ C₂ : ℝ),
      α₀ ≤ α → γ₀ ≤ γ → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ α) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ γ) →
      Integrable (coupledWeightedBlockKernel h c a F f W V f₁ f₂)
        (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod
          (rightTailProductMeasure (r + 1) (t + 1) ν μ₁ μ₂ κ))) := by
  have hV' : V ∈ realUniformWhittakerModel t es (-(-a)) := by simpa only [neg_neg] using hV
  let β := c.exponent.re + (r : ℝ) / 2
  let ω := ((r - t : ℕ) : ℝ) / 2
  obtain ⟨u₀, v₀, hInt⟩ := realGapOrdinaryConvergence r t h W V (hasGaugeBound_of_mem_model hW)
    (hasGaugeBound_of_mem_model hV) D ν νY μ₁ μ₂ κ inferInstance inferInstance inferInstance
  refine ⟨u₀ + ω, v₀ - β + ω, ?_⟩
  intro f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  let u := α - ω
  let v := γ + β - ω
  have hu : u₀ ≤ u := by dsimp only [u]; linarith
  have hv : v₀ ≤ v := by dsimp only [v]; linarith
  let K := coupledWeightedBlockKernel h c a F f W V f₁ f₂
  change Integrable K _
  rw [weighted_measure_eq]
  apply (integrable_withDensity_iff_integrable_coe_smul measurable_tailDensity).mpr
  have hC₁ := RapidDecay.nonneg_const h₁
  have hC₂ := RapidDecay.nonneg_const h₂
  have hM : Measurable K := measurable_coupledWeightedBlockKernel h c a F f Φ₀ Ξ Ψ hΦ hW hV' f₁ f₂ hm₁ hm₂
  refine hInt u v (β + (-α + γ) - ((t + 1 : ℕ) : ℝ)) hu hv Φ₀ Ξ Ψ (C₁ * C₂)
    (mul_nonneg hC₁ hC₂) (fun p => (tailDensity p : ℝ) • K p)
    (measurable_tailDensity.coe_nnreal_real.smul hM).aestronglyMeasurable (fun p => ?_)
  let B := tailOn h p.2
  let w := p.2.2.1.1.2
  let b := δ B
  have hb : 0 < b := abs_pos.mpr B.det_ne_zero
  have hw : 0 < δ w := abs_pos.mpr w.det_ne_zero
  have hb_eq : b = δ w :=
    realNormalizedAbs_det_rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) w p.2.2.1.2 p.2.2.2
  let g₁ (x : ℝ) := f₁ (x * b⁻¹)
  let g₂ (x : ℝ) := f₂ (x * b) * (x : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2))
  have hg₁ (x : ℝ) (hx : 0 < x) : ‖g₁ x‖ ≤ C₁ * b ^ (-α) * x ^ α := by
    have hh := h₁ (x * b⁻¹) (mul_pos hx (inv_pos.mpr hb))
    rw [Real.mul_rpow hx.le (inv_nonneg.mpr hb.le), Real.inv_rpow hb.le, ← Real.rpow_neg hb.le] at hh
    exact hh.trans_eq (by ring)
  have hg₂ (x : ℝ) (hx : 0 < x) : ‖g₂ x‖ ≤ C₂ * b ^ γ * x ^ (v - β) := by
    have hh := h₂ (x * b) (mul_pos hx hb)
    rw [Real.mul_rpow hx.le hb.le] at hh
    have hω : (-(((r - t : ℕ) : ℂ) / 2)).re = -ω := by
      simp only [ω, Complex.neg_re, Complex.div_ofNat_re, Complex.natCast_re]
    dsimp only [g₂]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hω]
    refine (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hx.le _)).trans_eq ?_
    calc
      _ = C₂ * b ^ γ * (x ^ γ * x ^ (-ω)) := by ring
      _ = _ := by rw [← Real.rpow_add hx, show γ + -ω = v - β by dsimp only [v]; ring]
  have hg₁' (x : ℝ) (hx : 0 < x) :
      ‖g₁ x‖ ≤ C₁ * b ^ (-α) * x ^ (u + ((r - t : ℕ) : ℝ) / 2) := by
    rw [show u + ((r - t : ℕ) : ℝ) / 2 = α by change α - ω + ω = α; ring]
    exact hg₁ x hx
  have hBound := norm_weightedBlockKernel_le h c a F f Φ₀ Ξ Ψ hΦ W V g₁ g₂ u v
    (C₁ * b ^ (-α)) (C₂ * b ^ γ) (mul_nonneg hC₂ (Real.rpow_nonneg hb.le _)) hg₁' hg₂ p
  have ht : 0 ≤ (tailDensity p : ℝ) := NNReal.coe_nonneg _
  rw [norm_smul, Real.norm_of_nonneg ht]
  refine (mul_le_mul_of_nonneg_left hBound ht).trans_eq ?_
  rw [tailDensity_eq, hb_eq]
  unfold ordinaryGapNorm
  rw [show β + (-α + γ) - ((t + 1 : ℕ) : ℝ) =
      β + ((-α + γ) + (-((t + 1 : ℕ) : ℝ))) by ring]
  rw [Real.rpow_add hw β _, Real.rpow_add hw (-α + γ) _, Real.rpow_add hw (-α) γ]
  ring

open RealGapNormalizedWeighted (quotientDetAbs_right)
open RealGodementBlockUnfolding (blockUnfoldedKernel beforeBlockKernel blockUnfoldedKernel_shift)
open ComplexGodementBlockUnfolding (quotientShift measurePreserving_quotientShift)
open RealGodementPaddedRestriction (paddedRestrictionKernel)
open RealGodementTwoBlockRestriction (twoBlockRestrictionKernel_chart)
open RealTwoBlockHaar (realTwoBlockRightHaar determinant_diagonalBlocks diagonalBlocks_eq_padGL
  lastRow_diagonalBlocks_mul)

local notation "Raw" => fun r t => Q t × (Y r t × G (r + 1))

/-- The weighted padded kernel on the quotient, rectangle and ambient group, before any Haar chart. -/
def coupledHaarKernel {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Sq r → ℂ) (f : Rows r → ℂ) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Raw r t) : ℂ :=
  let H := p.2.2
  F (H * lowerRectangle h p.2.1).val * realFourierTransform a f (Langlands.RankinSelberg.lastRow H⁻¹) *
    (detCharacter c.character.toMonoidHom H * P H ((r : ℂ) / 2)) *
    realUnequalIntegrand h (ρ H⁻¹ W) V 0 p.1 * f₁ (quotientDetAbs p.1 * (δ H)⁻¹) * f₂ (δ H)

/-- The ambient kernel reads the padded Godement integrand at the representative. -/
theorem coupledHaarKernel_eq {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Sq r → ℂ) (f : Rows r → ℂ) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Raw r t) :
    coupledHaarKernel h c a F f W V f₁ f₂ p =
      paddedRestrictionKernel c a F f W (padGL (Nat.succ_le_succ h.le) p.1.out)
        (lowerRectangle h p.2.1) p.2.2 * V p.1.out * P p.1.out (0 - ((r - t : ℕ) : ℂ) / 2) *
          f₁ (quotientDetAbs p.1 * (δ p.2.2)⁻¹) * f₂ (δ p.2.2) := by
  let b := p.2.2
  let g := p.1.out
  have hrow : Langlands.RankinSelberg.lastRow (padGL (Nat.succ_le_succ h.le) g * b⁻¹) =
      Langlands.RankinSelberg.lastRow b⁻¹ := by
    rw [← diagonalBlocks_eq_padGL (Nat.succ_pos t) (Nat.succ_lt_succ h)]
    exact lastRow_diagonalBlocks_mul (Nat.succ_pos t) (Nat.succ_lt_succ h) g b⁻¹
  unfold coupledHaarKernel paddedRestrictionKernel realUnequalIntegrand ArchimedeanLocal.unequalIntegrand
    ArchimedeanLocal.translateFunction
  dsimp only [b, g] at hrow
  rw [hrow]
  ring

set_option maxHeartbeats 1000000 in
private theorem measurable_coupledHaarKernel {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Sq r → ℂ) (f : Rows r → ℂ)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Rows r, ℂ)) (hΦ : HasSplitPartialTest h a F f Φ₀ Ξ Ψ)
    {ds es : List RealBlock} {W : G (r + 1) → ℂ} {V : G (t + 1) → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds (-a)) (hV : V ∈ realUniformWhittakerModel t es (-(-a)))
    (f₁ f₂ : ℝ → ℂ) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    Measurable (coupledHaarKernel h c a F f W V f₁ f₂) := by
  let he := Nat.succ_lt_succ h
  let x := fun p : Raw r t => p.2.1
  let b := fun p : Raw r t => p.2.2
  let C := fun p : Raw r t => b p * lowerRectangle h (x p)
  have hb : Continuous b := continuous_snd.comp continuous_snd
  have hx : Continuous x := continuous_fst.comp continuous_snd
  have hC : Continuous C := hb.mul ((continuous_lowerRectangle h).comp hx)
  have hRow : Continuous (fun p : Raw r t => Langlands.RankinSelberg.lastRow (b p)⁻¹) :=
    continuous_pi fun j => (Langlands.GeneralLinear.entry (R := ℝ) (Fin.last r) j).continuous.comp hb.inv
  have hB : Continuous (fun p : Raw r t => realUnequalIntegrand h (ρ (b p)⁻¹ W) V 0 p.1) := by
    apply ((leftQuotient_isOpenQuotientMap (N t)).prodMap
      (IsOpenQuotientMap.id (X := Y r t × G (r + 1)))).isQuotientMap.continuous_iff.mpr
    change Continuous (fun p : G (t + 1) × (Y r t × G (r + 1)) =>
      realUnequalIntegrand h (ρ p.2.2⁻¹ W) V 0 (Quotient.mk _ p.1))
    simp_rw [ordinaryKernel_mk h (left_translate (leftCharacter_of_mem hW) _) (leftCharacter_of_mem hV)]
    have hp := (UnequalAnalytic.continuous_padGL (Nat.succ_le_succ h.le)).comp
      (continuous_fst : Continuous (Prod.fst : G (t + 1) × (Y r t × G (r + 1)) → _))
    exact (((continuous_of_mem hW).comp (hp.mul (continuous_snd.comp continuous_snd).inv)).mul
      ((continuous_of_mem hV).comp continuous_fst)).mul ((continuous_detPower _).comp continuous_fst)
  have hK : coupledHaarKernel h c a F f W V f₁ f₂ = fun p =>
      Φ₀ (leadingColumns he (C p)) * Ξ (tailColumns he (C p)) *
        Ψ (Langlands.RankinSelberg.lastRow (b p)⁻¹) *
        (detCharacter c.character.toMonoidHom (b p) * P (b p) ((r : ℂ) / 2)) *
        realUnequalIntegrand h (ρ (b p)⁻¹ W) V 0 p.1 *
        f₁ (quotientDetAbs p.1 * (δ (b p))⁻¹) * f₂ (δ (b p)) := by
    funext p
    dsimp only [coupledHaarKernel]
    rw [hΦ.1, hΦ.2]
  rw [hK]
  have hδ : Measurable (fun p : Raw r t => δ (b p)) := (Units.continuous_val.comp hb).matrix_det.abs.measurable
  have hg : Measurable (fun p : Raw r t => quotientDetAbs p.1) :=
    continuous_quotientDetAbs.measurable.comp measurable_fst
  have h₁ := ((Φ₀.continuous.comp ((continuous_leadingColumns he).comp hC)).mul
    (Ξ.continuous.comp ((continuous_tailColumns he).comp hC))).mul (Ψ.continuous.comp hRow)
  have h₂ := ((continuous_detCharacter c).comp hb).mul ((continuous_detPower ((r : ℂ) / 2)).comp hb)
  exact ((((h₁.mul h₂).mul hB).measurable.mul (hf₁.comp (hg.mul hδ.inv))).mul (hf₂.comp hδ))

private def chartOn {r t : ℕ} (h : t < r) (p : Tail r t) : G (r + 1) :=
  rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) p.1.1.2 p.1.2 p.2 *
    diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) p.1.1.1 1

private theorem continuous_chartOn {r t : ℕ} (h : t < r) : Continuous (chartOn h) := by
  have hb := (continuous_tailOn h).comp
    ((continuous_const : Continuous (fun _ : Tail r t => (0 : Y r t))).prodMk continuous_id)
  have hz : Continuous (fun p : Tail r t => p.1.1.1) := by fun_prop
  exact hb.mul ((continuous_diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h)).comp
    (hz.prodMk continuous_const))

private theorem detAbs_chartOn {r t : ℕ} (h : t < r) (p : Coords r t) :
    δ (chartOn h p.2.2) = δ p.2.2.1.1.1 * δ (tailOn h p.2) := by
  let B := tailOn h p.2
  let z := p.2.2.1.1.1
  let A := diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) z 1
  have he : determinant (B * A) = determinant z * determinant B := by
    unfold A
    rw [map_mul, determinant_diagonalBlocks, map_one, mul_one, mul_comm]
  change realNormalizedAbs (determinant (B * A) : ℝ) =
    realNormalizedAbs (determinant z : ℝ) * realNormalizedAbs (determinant B : ℝ)
  rw [he]
  simp only [realNormalizedAbs, Units.val_mul, abs_mul]

private theorem detPower_eq_cpow {n : ℕ} (g : G n) (s : ℂ) : P g s = (δ g : ℂ) ^ s := by
  have hy : |g.val.det| ≠ 0 := abs_ne_zero.mpr g.det_ne_zero
  change Complex.exp (s * (Real.log |g.val.det| : ℂ)) = ((|g.val.det| : ℝ) : ℂ) ^ s
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy), ← Complex.ofReal_log (abs_nonneg _),
    mul_comm]

set_option maxHeartbeats 2000000 in
/-- Coupled Haar integrability for any two radial profiles bounded by independently large powers. -/
theorem realGapCoupledHaarPowerBounds (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t)
    (νY : AdditiveHaarMeasure ℝ) (μH : Measure (G (r + 1))) (κ : Measure (KU (r + 1)))
    [μH.IsHaarMeasure] [κ.IsHaarMeasure] (hκinv : κ.IsInvInvariant)
    (ds es : List RealBlock) (a : ℝˣ) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (hW : W ∈ realUniformWhittakerModel r ds (-a)) (hV : V ∈ realUniformWhittakerModel t es a)
    (c : RealCharacterData) (F : Sq r → ℂ) (f : Rows r → ℂ)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Rows r, ℂ)) (hΦ : HasSplitPartialTest h a F f Φ₀ Ξ Ψ) :
    ∃ α₀ γ₀ : ℝ, ∀ (f₁ f₂ : ℝ → ℂ) (α γ C₁ C₂ : ℝ),
      α₀ ≤ α → γ₀ ≤ γ → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ α) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ γ) →
      Integrable (coupledHaarKernel h c a F f W V f₁ f₂)
       (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod μH)) := by
  let μ₁ : Measure (G (t + 1)) := Measure.haar
  let μ₂ : Measure (G (r + 1 - (t + 1))) := Measure.haar
  let ν := νY
  obtain ⟨α₀, γ₀, hI⟩ := realGapCoupledPowerBounds r t h D ν νY μ₁ μ₂ κ ds es a W V hW hV c F f
    Φ₀ Ξ Ψ hΦ
  refine ⟨α₀, γ₀, ?_⟩
  intro f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  have hV' : V ∈ realUniformWhittakerModel t es (-(-a)) := by simpa only [neg_neg] using hV
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : SigmaCompactSpace (Q t) := by
    let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
    have e := leftQuotient_isOpenQuotientMap (N t)
    rw [← isSigmaCompact_univ_iff, ← Set.range_eq_univ.mpr e.surjective]
    exact isSigmaCompact_range e.continuous
  let R := rightTailProductMeasure (r + 1) (t + 1) ν μ₁ μ₂ κ
  let X := rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)
  let : X.IsAddHaarMeasure := rectangularMeasure_isAddHaar νY _ _
  let : SigmaFinite X := inferInstance
  let R₀ := (((μ₁.prod μ₂).prod (rectangularMeasure ν (t + 1) (r + 1 - (t + 1)))).prod κ)
  let : (rectangularMeasure ν (t + 1) (r + 1 - (t + 1))).IsAddHaarMeasure := rectangularMeasure_isAddHaar ν _ _
  let : SigmaFinite R₀ := inferInstance
  let : SigmaFinite R := SigmaFinite.withDensity_of_ne_top (ae_of_all R₀ fun (_ : Tail r t) => ENNReal.coe_ne_top)
  let K := coupledHaarKernel h c a F f W V f₁ f₂
  let chrom := chartOn h
  let eChart : Coords r t → Raw r t := Prod.map id (Prod.map id chrom)
  have hChart := (MeasurePreserving.id D.measure).prod ((MeasurePreserving.id X).prod
    (show MeasurePreserving chrom R (R.map chrom) from ⟨(continuous_chartOn h).measurable, rfl⟩))
  let leading := fun p : Par r t => p.2.1.1.1
  have hl : Measurable leading := by fun_prop
  let e := quotientShift (N t) leading hl
  have he := measurePreserving_quotientShift (N t) D.measure (X.prod R) D.compatible.right_invariant
    leading hl
  have hF := hI f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  have hpull (p : Coords r t) : K (eChart (e p)) = coupledWeightedBlockKernel h c a F f W V f₁ f₂ p := by
    let z := p.2.2.1.1.1
    let b := δ (tailOn h p.2)
    have hb : 0 < b := abs_pos.mpr (tailOn h p.2).det_ne_zero
    have hz : 0 < δ z := abs_pos.mpr z.det_ne_zero
    let q := (e p).1
    have hq : quotientDetAbs q = δ z * quotientDetAbs p.1 := quotientDetAbs_right p.1 z
    have hδ : δ (chrom p.2.2) = δ z * b := detAbs_chartOn h p
    have hrad : quotientDetAbs q * (δ (chrom p.2.2))⁻¹ = quotientDetAbs p.1 * b⁻¹ := by
      rw [hq, hδ]
      field_simp [hz.ne', hb.ne']
    have hback : Langlands.QuotientIntegration.rightTranslate (N t) z⁻¹ q = p.1 := by
      change Langlands.QuotientIntegration.rightTranslate (N t) z⁻¹
        (Langlands.QuotientIntegration.rightTranslate (N t) z p.1) = p.1
      rw [Langlands.QuotientIntegration.rightTranslate_mul, mul_inv_cancel,
        Langlands.QuotientIntegration.rightTranslate_one]
    have hBase := blockUnfoldedKernel_shift h c a F f W V (leftCharacter_of_mem hW)
      (leftCharacter_of_mem hV) 0 (e p)
    change blockUnfoldedKernel h c a F f W V 0
      (Langlands.QuotientIntegration.rightTranslate (N t) z⁻¹ q, p.2) =
        beforeBlockKernel h c a F f W V 0 (q, p.2) at hBase
    rw [hback] at hBase
    change coupledHaarKernel h c a F f W V f₁ f₂ (q, p.2.1, chrom p.2.2) = _
    rw [coupledHaarKernel_eq]
    dsimp only [chrom, chartOn]
    rw [twoBlockRestrictionKernel_chart (Nat.succ_pos t) (Nat.succ_lt_succ h)]
    change beforeBlockKernel h c a F f W V 0 (q, p.2) *
      f₁ (quotientDetAbs q * (δ (chrom p.2.2))⁻¹) * f₂ (δ (chrom p.2.2)) = _
    rw [← hBase, hrad, hδ]
    unfold blockUnfoldedKernel coupledWeightedBlockKernel weightedBlockKernel weightedOrdinary
    dsimp only
    rw [detPower_eq_cpow z (0 - ((r - t : ℕ) : ℂ) / 2)]
    simp only [zero_sub, b, z]
    unfold tailOn
    ring
  have hpre : Integrable (K ∘ eChart) (D.measure.prod (X.prod R)) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).mp
    change Integrable (fun p => K (eChart (e p))) _
    simp_rw [hpull]
    exact hF
  have hm := measurable_coupledHaarKernel h c a F f Φ₀ Ξ Ψ hΦ hW hV' f₁ f₂ hm₁ hm₂
  have hR : Integrable K (D.measure.prod (X.prod (R.map chrom))) :=
    (hChart.integrable_comp hm.aestronglyMeasurable).mp hpre
  obtain ⟨cH, hc, hH⟩ := realTwoBlockRightHaar (r + 1) (t + 1) (Nat.succ_pos t)
    (Nat.succ_lt_succ h) ν μH μ₁ μ₂ κ inferInstance inferInstance inferInstance inferInstance hκinv
  change μH = cH • R.map chrom at hH
  rw [hH, Measure.prod_smul_right, Measure.prod_smul_right]
  exact hR.smul_measure_nnreal

/-- The full weighted ambient kernel is jointly integrable, without fixing either rectangle
or the ambient Haar variable. -/
def RealGapCoupledHaarStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t) (νY : AdditiveHaarMeasure ℝ)
    (μH : Measure (G (r + 1))) (κ : Measure (KU (r + 1))), μH.IsHaarMeasure → κ.IsHaarMeasure →
    κ.IsInvInvariant →
    ∀ (ds es : List RealBlock) (a : ℝˣ) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ),
      W ∈ realUniformWhittakerModel r ds (-a) → V ∈ realUniformWhittakerModel t es a →
    ∀ (c : RealCharacterData) (F : Sq r → ℂ) (f : Rows r → ℂ)
      (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
      (Ψ : 𝓢(Rows r, ℂ)), HasSplitPartialTest h a F f Φ₀ Ξ Ψ →
    ∀ (f₁ f₂ : ℝ → ℂ), Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
    Integrable (coupledHaarKernel h c a F f W V f₁ f₂)
      (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod μH))

theorem realGapCoupledHaar : RealGapCoupledHaarStatement := by
  intro r t h D νY μH κ hμH hκ hκinv ds es a W V hW hV c F f Φ₀ Ξ Ψ hΦ f₁ f₂ hm₁ hm₂ hf₁ hf₂
  obtain ⟨α, γ, hI⟩ := realGapCoupledHaarPowerBounds r t h D νY μH κ hκinv ds es a W V hW hV c F f
    Φ₀ Ξ Ψ hΦ
  obtain ⟨C₁, h₁⟩ := hf₁ α
  obtain ⟨C₂, h₂⟩ := hf₂ γ
  exact hI f₁ f₂ α γ C₁ C₂ le_rfl le_rfl hm₁ hm₂ h₁ h₂

end Langlands.Global.RankinSelbergGlobal.RealGapOrdinaryWeighted
