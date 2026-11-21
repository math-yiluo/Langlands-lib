import Langlands.Global.RankinSelberg.ComplexGapOrdinaryConvergence
import Langlands.Global.RankinSelberg.ComplexGapSplitTestColumns
import Langlands.Global.RankinSelberg.ComplexGodementBlockUnfolding
import Langlands.Global.RankinSelberg.ComplexGapNormalizedWeighted
import Langlands.Global.RankinSelberg.ComplexTwoBlockRightHaar

/-! # Rapid determinant weights on the ordinary complex gap kernel -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinaryWeighted

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant determinantContinuous lowerBlockPair continuous_lowerBlockPair reindexContinuous)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rectangularJoin continuous_rectangularJoin)
open Langlands.GodementJacquet (complexAbsHom continuous_complexAbsHom)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexUnequalIntegrand)
open ArchimedeanMellinPair (RapidDecay)
open ComplexGapOrdinaryConvergence (ordinaryGapProductMeasure complexGapOrdinaryConvergence)
open ComplexGapOrdinaryMajorant (ordinaryGapNorm)
open ComplexGapSplitTestColumns (leadingColumns complexGapSplitTestColumns)
open ComplexGodement (characterWeight continuous_characterWeight norm_characterWeight)
open ComplexGodementLowerRectangle (lowerRectangle)
open ComplexGodementPartialFourier (partialSchwartz)
open ComplexGodementTwoBlockRestriction (rightTailProductMeasure)
open ComplexTwoBlockHaar (rightTail rightTailWeight diagonalBlocks tailColumns
  continuous_diagonalBlocks continuous_upperRectangle complexNormalizedAbs_det_rightTail)
open ComplexUnequalFamily (HasLeftCharacter ordinaryKernel_mk)
open ComplexUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary)
open RealConvergenceAnalysis (norm_cexp_mul_ofReal)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "N" => fun t => Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ
local notation "XR" => fun r t => Mat (t + 1) (r + 1 - (t + 1))
local notation "Y" => fun r t => Mat (r + 1 - (t + 1)) (t + 1)
local notation "Tail" => fun r t => (((G (t + 1) × G (r + 1 - (t + 1))) × XR r t) × KU (r + 1))
local notation "Par" => fun r t => Y r t × Tail r t
local notation "Coords" => fun r t => Q t × Par r t
local notation "Test" => fun r => SchwartzMap (Mat (r + 1) (r + 2)) ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

local instance gapWeightedGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapWeightedGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapWeightedGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
local instance gapWeightedGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
local instance gapWeightedMatrixBorel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℂ))
local instance gapWeightedMatrixSecondCountable (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℂ))
local instance gapWeightedKUSecondCountable (n : ℕ) : SecondCountableTopology (KU n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance gapWeightedKUOpens (n : ℕ) : OpensMeasurableSpace (KU n) :=
  Subtype.opensMeasurableSpace (fun g : G n => g ∈ unitaryCompact ℂ n)
local instance gapWeightedQSecondCountable (t : ℕ) : SecondCountableTopology (Q t) :=
  TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (N t)).isOpenMap
attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

private def tailOn {r t : ℕ} (h : t < r) (p : Par r t) : G (r + 1) :=
  rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) p.2.1.1.2 p.2.1.2 p.2.2

set_option maxHeartbeats 700000 in
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
  exact (reindexContinuous (R := ℂ) (finCongr (Nat.add_sub_of_le (Nat.succ_le_succ h.le)))).continuous.comp
    (continuous_lowerBlockPair.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const)))

private theorem continuous_detPower {n : ℕ} (s : ℂ) :
    Continuous (fun g : G n => ArchimedeanLocal.detPower complexNormalizedAbs g s) := by
  have hδ : Continuous (fun g : G n => δ g) := (Units.continuous_val.matrix_det.norm).pow 2
  have hlog := hδ.log fun g => (pow_ne_zero 2 (norm_ne_zero_iff.mpr g.det_ne_zero))
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

private theorem left_translate_model {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) (x : G (r + 1)) : HasLeftCharacter a (ρ x W.val) := by
  intro u g
  change W.val ((u.val * g) * x) = _
  rw [mul_assoc, complexWhittakerModel_left_equivariant W.2 _ u.2]
  rfl

open scoped Matrix.Norms.Operator in
private theorem continuous_model {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) : Continuous W.val :=
  (contMDiff_of_mem_complexWhittakerModel W.2).continuous

private theorem continuous_translated_product {r t : ℕ} (h : t < r) {ds es : List ComplexCharacterData}
    {a : ℂˣ} (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)) :
    Continuous (fun p : Coords r t => complexUnequalIntegrand h
      (ρ (tailOn h p.2)⁻¹ W.val) (ρ p.2.2.1.1.1 V.val) 0 p.1) := by
  apply ((leftQuotient_isOpenQuotientMap (N t)).prodMap (IsOpenQuotientMap.id (X := Par r t))).isQuotientMap.continuous_iff.mpr
  change Continuous (fun p : G (t + 1) × Par r t => complexUnequalIntegrand h
    (ρ (tailOn h p.2)⁻¹ W.val) (ρ p.2.2.1.1.1 V.val) 0 (Quotient.mk _ p.1))
  simp_rw [ordinaryKernel_mk h (left_translate_model W _) (left_translate_model V _)]
  have hg : Continuous (fun p : G (t + 1) × Par r t => padGL (Nat.succ_le_succ h.le) p.1 * (tailOn h p.2)⁻¹) :=
    ((UnequalAnalytic.continuous_padGL (Nat.succ_le_succ h.le)).comp continuous_fst).mul
      ((continuous_tailOn h).comp continuous_snd).inv
  exact (((continuous_model W).comp hg).mul ((continuous_model V).comp (by fun_prop))).mul
    ((continuous_detPower _).comp continuous_fst)

private def godementExponent (r : ℕ) (s : ℂ) : ℂ := (((r + 2 : ℕ) : ℂ) / 2 + s - 1)

/-- The ordinary block kernel after the quotient change of variables, with independent
rapid radial weights on the quotient argument and the leading group variable. -/
def weightedBlockKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : Test r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Coords r t) : ℂ :=
  let z := p.2.2.1.1.1
  let B := tailOn h p.2
  let A := diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) z 1
  partialSchwartz a μ Φ (rectangularJoin (B.val * A.val * (lowerRectangle h p.2.1).val)
    (B⁻¹.val (Fin.last r))) * characterWeight d (godementExponent r s) (determinant B) *
    (characterWeight d (godementExponent r s) (determinant z) * f₂ (δ z)) *
    weightedOrdinary h (ρ B⁻¹ W) (ρ z V) f₁ p.1

private theorem measurable_weightedBlockKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test r) {ds es : List ComplexCharacterData}
    (W : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel t es (-(-a))) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    Measurable (weightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂) := by
  let B := fun p : Coords r t => tailOn h p.2
  let z := fun p : Coords r t => p.2.2.1.1.1
  let A := fun p : Coords r t => diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) (z p) 1
  have hB : Continuous B := (continuous_tailOn h).comp continuous_snd
  have hz : Continuous z := by fun_prop
  have hA : Continuous A := (continuous_diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h)).comp
    (hz.prodMk continuous_const)
  have hy : Continuous (fun p : Coords r t => lowerRectangle h p.2.1) :=
    (continuous_lowerRectangle h).comp (continuous_fst.comp continuous_snd)
  have hInv : Continuous (fun p : Coords r t => (B p)⁻¹) := hB.inv
  have hRow : Continuous (fun p : Coords r t => (B p)⁻¹.val (Fin.last r)) :=
    continuous_pi fun j => (Langlands.GeneralLinear.entry (R := ℂ) (Fin.last r) j).continuous.comp hInv
  have hZ : Continuous (fun p : Coords r t => rectangularJoin ((B p).val * (A p).val * (lowerRectangle h p.2.1).val)
      ((B p)⁻¹.val (Fin.last r))) :=
    continuous_rectangularJoin.comp ((((Units.continuous_val.comp hB).matrix_mul (Units.continuous_val.comp hA)).matrix_mul
      (Units.continuous_val.comp hy)).prodMk hRow)
  have hχB := (continuous_characterWeight d (godementExponent r s)).comp ((determinantContinuous (n := r + 1) (R := ℂ)).continuous.comp hB)
  have hχz := (continuous_characterWeight d (godementExponent r s)).comp ((determinantContinuous (n := t + 1) (R := ℂ)).continuous.comp hz)
  have hδz : Continuous (fun p : Coords r t => δ (z p)) := (Units.continuous_val.comp hz).matrix_det.norm.pow 2
  exact (((partialSchwartz a μ Φ).continuous.comp hZ).measurable.mul hχB.measurable).mul
    (hχz.measurable.mul (hf₂.comp hδz.measurable)) |>.mul
    ((continuous_translated_product h W V).measurable.mul (hf₁.comp (continuous_quotientDetAbs.measurable.comp measurable_fst)))

/-- Splitting the partial Fourier test into its leading columns, trailing columns and
last frequency gives the three Schwartz factors used in the ordinary convergence proof. -/
def HasSplitPartialTest {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (Φ : Test r)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)) : Prop :=
  ∀ (C : G (r + 1)) (v : Fin (r + 1) → ℂ),
    partialSchwartz a μ Φ (rectangularJoin C.val v) =
      Φ₀ (leadingColumns (Nat.succ_lt_succ h) C) * Ξ (tailColumns (Nat.succ_lt_succ h) C) * Ψ v

private def tailDensity {r t : ℕ} (p : Coords r t) : ℝ≥0 :=
  rightTailWeight (k := t + 1) p.2.2.1.1.2

private theorem measurable_tailDensity {r t : ℕ} : Measurable (tailDensity (r := r) (t := t)) :=
  ((continuous_complexAbsHom.comp Units.continuous_val.matrix_det).pow _).measurable.inv.comp (by fun_prop)

private theorem tailDensity_eq {r t : ℕ} (p : Coords r t) :
    (tailDensity p : ℝ) = δ p.2.2.1.1.2 ^ (-((t + 1 : ℕ) : ℝ)) := by
  let q := δ p.2.2.1.1.2
  have hq : 0 ≤ q := pow_nonneg (norm_nonneg _) _
  change (q ^ (t + 1))⁻¹ = q ^ (-((t + 1 : ℕ) : ℝ))
  rw [Real.rpow_neg hq, Real.rpow_natCast]

private theorem weighted_measure_eq {r t : ℕ} (D : ComplexQuotientMeasureData t) (ν νY : AdditiveHaarMeasure ℂ)
    (κ : Measure (KU (r + 1))) [κ.IsHaarMeasure] :
    D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod
      (rightTailProductMeasure (r + 1) (t + 1) ν κ)) =
    (ordinaryGapProductMeasure r t D ν νY κ).withDensity (fun p => (tailDensity p : ℝ≥0∞)) := by
  let mTail := ((((complexGeneralLinearHaar (t + 1)).prod (complexGeneralLinearHaar (r + 1 - (t + 1)))).prod
    (rectangularMeasure ν (t + 1) (r + 1 - (t + 1)))).prod κ)
  let mY := rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)
  let θ := fun p : Tail r t => ((rightTailWeight (k := t + 1) p.1.1.2 : ℝ≥0) : ℝ≥0∞)
  let : (rectangularMeasure ν (t + 1) (r + 1 - (t + 1))).IsAddHaarMeasure := rectangularMeasure_isAddHaar ν _ _
  let : mY.IsAddHaarMeasure := rectangularMeasure_isAddHaar νY _ _
  let : CompactSpace (KU (r + 1)) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : SigmaFinite mTail := inferInstance
  let : SigmaFinite mY := inferInstance
  let : SigmaFinite (mY.prod mTail) := inferInstance
  have hθ : Measurable θ :=
    (((continuous_complexAbsHom.comp Units.continuous_val.matrix_det).pow (t + 1)).measurable.inv.coe_nnreal_ennreal).comp (by fun_prop)
  have hθ' : Measurable (fun p : Par r t => θ p.2) := hθ.comp measurable_snd
  change D.measure.prod (mY.prod (mTail.withDensity θ)) = (D.measure.prod (mY.prod mTail)).withDensity _
  rw [prod_withDensity_right hθ, prod_withDensity_right hθ']
  rfl

private theorem norm_detPower {n : ℕ} (g : G n) (s : ℂ) :
    ‖ArchimedeanLocal.detPower complexNormalizedAbs g s‖ = δ g ^ s.re := by
  dsimp only
  have hp : 0 < δ g := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Real.rpow_def_of_pos hp, mul_comm]

private theorem norm_weightedBlockKernel_le {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test r)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (hΦ : HasSplitPartialTest h μ a Φ Φ₀ Ξ Ψ)
    (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (s : ℂ) (f₁ f₂ : ℝ → ℂ)
    (u v C₁ C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hf₁ : ∀ x : ℝ, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ (u + ((r - t : ℕ) : ℝ) / 2))
    (hf₂ : ∀ x : ℝ, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ (v - (d.exponent + godementExponent r s).re))
    (p : Coords r t) :
    ‖weightedBlockKernel h μ d a Φ W V s f₁ f₂ p‖ ≤
      (C₁ * C₂) * ordinaryGapNorm h Φ₀ Ξ Ψ W V u v (d.exponent + godementExponent r s).re
        p.1.out p.2.2.1.1.1 p.2.2.1.1.2 p.2.2.1.2 p.2.1 p.2.2.2 := by
  let g := p.1.out
  let z := p.2.2.1.1.1
  let w := p.2.2.1.1.2
  let B := tailOn h p.2
  let k := Nat.succ_pos t
  let l := Nat.succ_lt_succ h
  let A := diagonalBlocks k l z 1
  let C := B * A * lowerRectangle h p.2.1
  let β := (d.exponent + godementExponent r s).re
  let ω := ((r - t : ℕ) : ℝ) / 2
  have hg : 0 < δ g := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  have hz : 0 < δ z := pow_pos (norm_pos_iff.mpr z.det_ne_zero) _
  have hw : 0 < δ w := pow_pos (norm_pos_iff.mpr w.det_ne_zero) _
  have hA : C.val = B.val * A.val * (lowerRectangle h p.2.1).val := rfl
  obtain ⟨hL, hT⟩ := complexGapSplitTestColumns r t h B z p.2.1
  have hTest := hΦ C (B⁻¹.val (Fin.last r))
  rw [hA, hL, hT] at hTest
  simp only [show ∀ x y z : ℂ, (x * y) * z = x * (y * z) from mul_assoc] at hTest
  have hχB : ‖characterWeight d (godementExponent r s) (determinant B)‖ = δ w ^ β := by
    rw [norm_characterWeight]
    change δ B ^ β = δ w ^ β
    dsimp only
    rw [show complexNormalizedAbs B.val.det = complexNormalizedAbs w.val.det from
      complexNormalizedAbs_det_rightTail k l w p.2.2.1.2 p.2.2.2]
  have hχz : ‖characterWeight d (godementExponent r s) (determinant z) * f₂ (δ z)‖ ≤ C₂ * δ z ^ v := by
    rw [norm_mul, norm_characterWeight]
    change δ z ^ β * ‖f₂ (δ z)‖ ≤ _
    calc
      _ ≤ δ z ^ β * (C₂ * δ z ^ (v - β)) :=
        mul_le_mul_of_nonneg_left (hf₂ _ hz) (Real.rpow_nonneg hz.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hz]; congr 2; ring
  have hPow : ‖ArchimedeanLocal.detPower complexNormalizedAbs g (0 - ((r - t : ℕ) : ℂ) / 2)‖ = δ g ^ (-ω) := by
    rw [norm_detPower]
    have he : (0 : ℂ) - ((r - t : ℕ) : ℂ) / 2 = ((-ω : ℝ) : ℂ) := by
      dsimp only [ω]
      push_cast
      ring
    rw [he, Complex.ofReal_re]
  have hOrd : ‖weightedOrdinary h (ρ B⁻¹ W) (ρ z V) f₁ p.1‖ ≤
      ‖W (padGL l.le g * B⁻¹)‖ * ‖V (g * z)‖ * (C₁ * δ g ^ u) := by
    unfold weightedOrdinary complexUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction
    simp only [norm_mul]
    change ‖W (padGL l.le g * B⁻¹)‖ * ‖V (g * z)‖ *
      ‖ArchimedeanLocal.detPower complexNormalizedAbs g (0 - ((r - t : ℕ) : ℂ) / 2)‖ * ‖f₁ (δ g)‖ ≤ _
    rw [hPow, mul_assoc (‖W (padGL l.le g * B⁻¹)‖ * ‖V (g * z)‖)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc
      _ ≤ δ g ^ (-ω) * (C₁ * δ g ^ (u + ω)) :=
        mul_le_mul_of_nonneg_left (hf₁ _ hg) (Real.rpow_nonneg hg.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hg]; congr 2; ring
  unfold weightedBlockKernel
  dsimp only
  change ‖partialSchwartz a μ Φ (rectangularJoin (B.val * A.val * (lowerRectangle h p.2.1).val)
      (B⁻¹.val (Fin.last r))) * characterWeight d (godementExponent r s) (determinant B) *
      (characterWeight d (godementExponent r s) (determinant z) * f₂ (δ z)) *
      weightedOrdinary h (ρ B⁻¹ W) (ρ z V) f₁ p.1‖ ≤ _
  rw [hTest, norm_mul, norm_mul, norm_mul, hχB, norm_mul]
  have hβ := Real.rpow_nonneg hw.le β
  have hv := Real.rpow_nonneg hz.le v
  refine (mul_le_mul (mul_le_mul_of_nonneg_left hχz (by positivity)) hOrd (norm_nonneg _)
    (by positivity)).trans_eq ?_
  dsimp only [ordinaryGapNorm, B, tailOn, g, z, w]
  ring

/-- The exact ordinary block kernel with rapid radial weights is jointly integrable
under the genuine right-tail chart density and the compatible outer quotient measure. -/
def ComplexGapOrdinaryWeightedStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t) (ν νY μ : AdditiveHaarMeasure ℂ)
    (κ : Measure (KU (r + 1))), κ.IsHaarMeasure →
    ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds (-a))
      (V : complexWhittakerModel t es a) (d : ComplexCharacterData) (Φ : Test r)
      (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
      (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)), HasSplitPartialTest h μ a Φ Φ₀ Ξ Ψ →
    ∀ (s : ℂ) (f₁ f₂ : ℝ → ℂ), Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
    Integrable (weightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂)
      (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod
        (rightTailProductMeasure (r + 1) (t + 1) ν κ)))

set_option maxHeartbeats 1200000 in
theorem complexGapOrdinaryWeighted : ComplexGapOrdinaryWeightedStatement := by
  intro r t h D ν νY μ κ hκ ds es a W V d Φ Φ₀ Ξ Ψ hΦ s f₁ f₂ hm₁ hm₂ hf₁ hf₂
  let V' : complexWhittakerModel t es (-(-a)) := ⟨V.val, by simpa only [neg_neg] using V.2⟩
  let : κ.IsHaarMeasure := hκ
  let β := (d.exponent + godementExponent r s).re
  let F := weightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂
  change Integrable F _
  rw [weighted_measure_eq]
  apply (integrable_withDensity_iff_integrable_coe_smul measurable_tailDensity).mpr
  obtain ⟨u, v, hInt⟩ := complexGapOrdinaryConvergence r t h ds es (-a) W V' D ν νY κ hκ
  obtain ⟨C₁, h₁⟩ := hf₁ (u + ((r - t : ℕ) : ℝ) / 2)
  obtain ⟨C₂, h₂⟩ := hf₂ (v - β)
  have hC₁ := RapidDecay.nonneg_const h₁
  have hC₂ := RapidDecay.nonneg_const h₂
  have hM : Measurable F := measurable_weightedBlockKernel h μ d a Φ W V' s f₁ f₂ hm₁ hm₂
  refine hInt u v (β - ((t + 1 : ℕ) : ℝ)) le_rfl le_rfl Φ₀ Ξ Ψ (C₁ * C₂) (mul_nonneg hC₁ hC₂)
    (fun p => (tailDensity p : ℝ) • F p) (measurable_tailDensity.coe_nnreal_real.smul hM).aestronglyMeasurable
    (fun p => ?_)
  have ht : 0 ≤ (tailDensity p : ℝ) := NNReal.coe_nonneg _
  have hb := norm_weightedBlockKernel_le h μ d a Φ Φ₀ Ξ Ψ hΦ W.val V.val s f₁ f₂ u v C₁ C₂ hC₂ h₁ h₂ p
  let w := p.2.2.1.1.2
  have hw : 0 < δ w := pow_pos (norm_pos_iff.mpr w.det_ne_zero) _
  rw [norm_smul, Real.norm_of_nonneg ht]
  refine (mul_le_mul_of_nonneg_left hb ht).trans_eq ?_
  rw [tailDensity_eq]
  unfold ordinaryGapNorm
  dsimp only
  rw [show β - ((t + 1 : ℕ) : ℝ) = β + (-((t + 1 : ℕ) : ℝ)) from sub_eq_add_neg _ _, Real.rpow_add hw]
  ring

/-- The two rapid radial weights before normalization of the retained determinant, written
in the right-tail chart after the quotient shear. -/
def coupledWeightedBlockKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : Test r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Coords r t) : ℂ :=
  let b := δ (tailOn h p.2)
  weightedBlockKernel h μ d a Φ W V s (fun x => f₁ (x * b⁻¹))
    (fun x => f₂ (x * b) * (x : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2))) p

private theorem measurable_coupledWeightedBlockKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test r) {ds es : List ComplexCharacterData}
    (W : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel t es (-(-a))) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    Measurable (coupledWeightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂) := by
  let F := weightedBlockKernel h μ d a Φ W.val V.val s (fun _ => 1) (fun _ => 1)
  let b (p : Coords r t) := δ (tailOn h p.2)
  let z (p : Coords r t) := δ p.2.2.1.1.1
  let x (p : Coords r t) := quotientDetAbs p.1
  have hB : Measurable b := ((Units.continuous_val.comp (continuous_tailOn h)).matrix_det.norm.pow 2).measurable.comp
    measurable_snd
  have hz : Measurable z := by dsimp only [z, complexNormalizedAbs]; fun_prop
  have hx : Measurable x := continuous_quotientDetAbs.measurable.comp measurable_fst
  have hp : Measurable (fun p => (z p : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2))) :=
    (Complex.measurable_ofReal.comp hz).pow_const _
  have hF : Measurable F := measurable_weightedBlockKernel h μ d a Φ W V s _ _ measurable_const measurable_const
  convert ((hF.mul (hf₁.comp (hx.mul hB.inv))).mul (hf₂.comp (hz.mul hB))).mul hp using 1
  funext p
  change _ = F p * f₁ (x p * (b p)⁻¹) * f₂ (z p * b p) * (z p : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2))
  unfold coupledWeightedBlockKernel F weightedBlockKernel weightedOrdinary
  dsimp only [x, z, b]
  ring

/-- Joint integrability also holds when the weights are evaluated at the quotient determinant
scaled down by the retained determinant and the leading determinant scaled up by it. -/
def ComplexGapCoupledWeightedStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t) (ν νY μ : AdditiveHaarMeasure ℂ)
    (κ : Measure (KU (r + 1))), κ.IsHaarMeasure →
    ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds (-a))
      (V : complexWhittakerModel t es a) (d : ComplexCharacterData) (Φ : Test r)
      (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
      (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)), HasSplitPartialTest h μ a Φ Φ₀ Ξ Ψ →
    ∀ (s : ℂ) (f₁ f₂ : ℝ → ℂ), Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
    Integrable (coupledWeightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂)
      (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod
        (rightTailProductMeasure (r + 1) (t + 1) ν κ)))

set_option maxHeartbeats 1500000 in
/-- The coupled right-tail estimate accepts independently chosen sufficiently large powers. -/
theorem complexGapCoupledPowerBounds (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t)
    (ν νY μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1))) (hκ : κ.IsHaarMeasure)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds (-a))
    (V : complexWhittakerModel t es a) (d : ComplexCharacterData) (Φ : Test r)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (hΦ : HasSplitPartialTest h μ a Φ Φ₀ Ξ Ψ) (s : ℂ) :
    ∃ α₀ γ₀ : ℝ, ∀ (f₁ f₂ : ℝ → ℂ) (α γ C₁ C₂ : ℝ),
      α₀ ≤ α → γ₀ ≤ γ → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ α) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ γ) →
      Integrable (coupledWeightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂)
        (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod
          (rightTailProductMeasure (r + 1) (t + 1) ν κ))) := by
  let V' : complexWhittakerModel t es (-(-a)) := ⟨V.val, by simpa only [neg_neg] using V.2⟩
  let : κ.IsHaarMeasure := hκ
  let β := (d.exponent + godementExponent r s).re
  let ω := ((r - t : ℕ) : ℝ) / 2
  obtain ⟨u₀, v₀, hInt⟩ := complexGapOrdinaryConvergence r t h ds es (-a) W V' D ν νY κ hκ
  refine ⟨u₀ + ω, v₀ - β + ω, ?_⟩
  intro f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  let u := α - ω
  let v := γ + β - ω
  have hu : u₀ ≤ u := by dsimp only [u]; linarith
  have hv : v₀ ≤ v := by dsimp only [v]; linarith
  let F := coupledWeightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂
  change Integrable F _
  rw [weighted_measure_eq]
  apply (integrable_withDensity_iff_integrable_coe_smul measurable_tailDensity).mpr
  have hC₁ := RapidDecay.nonneg_const h₁
  have hC₂ := RapidDecay.nonneg_const h₂
  have hM : Measurable F := measurable_coupledWeightedBlockKernel h μ d a Φ W V' s f₁ f₂ hm₁ hm₂
  refine hInt u v (β + (-α + γ) - ((t + 1 : ℕ) : ℝ)) hu hv Φ₀ Ξ Ψ (C₁ * C₂)
    (mul_nonneg hC₁ hC₂) (fun p => (tailDensity p : ℝ) • F p)
    (measurable_tailDensity.coe_nnreal_real.smul hM).aestronglyMeasurable (fun p => ?_)
  let B := tailOn h p.2
  let w := p.2.2.1.1.2
  let b := δ B
  have hb : 0 < b := pow_pos (norm_pos_iff.mpr B.det_ne_zero) _
  have hw : 0 < δ w := pow_pos (norm_pos_iff.mpr w.det_ne_zero) _
  have hb_eq : b = δ w :=
    complexNormalizedAbs_det_rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) w p.2.2.1.2 p.2.2.2
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
  have hBound := norm_weightedBlockKernel_le h μ d a Φ Φ₀ Ξ Ψ hΦ W.val V.val s g₁ g₂ u v
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

theorem complexGapCoupledWeighted : ComplexGapCoupledWeightedStatement := by
  intro r t h D ν νY μ κ hκ ds es a W V d Φ Φ₀ Ξ Ψ hΦ s f₁ f₂ hm₁ hm₂ hf₁ hf₂
  obtain ⟨α, γ, hI⟩ := complexGapCoupledPowerBounds r t h D ν νY μ κ hκ ds es a W V d Φ Φ₀ Ξ Ψ hΦ s
  obtain ⟨C₁, h₁⟩ := hf₁ α
  obtain ⟨C₂, h₂⟩ := hf₂ γ
  exact hI f₁ f₂ α γ C₁ C₂ le_rfl le_rfl hm₁ hm₂ h₁ h₂

open ComplexGapNormalizedWeighted (quotientDetAbs_right)
open ComplexGodementBlockUnfolding (blockUnfoldedKernel beforeBlockKernel blockUnfoldedKernel_shift
  quotientShift measurePreserving_quotientShift)
open ComplexGodementPaddedRestriction (paddedRestrictionKernel normPower_determinant)
open ComplexGodementTwoBlockRestriction (twoBlockRestrictionKernel_chart)
open ComplexTwoBlockHaar (complexTwoBlockRightHaar determinant_diagonalBlocks diagonalBlocks_eq_padGL
  lastRow_diagonalBlocks_mul)
open ArchimedeanRealPairIdentity (ofReal_cpow_eq_exp)

local notation "Raw" => fun r t => Q t × (Y r t × G (r + 1))
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

/-- The weighted padded kernel on the quotient, rectangle and ambient group, before any Haar chart. -/
def coupledHaarKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : Test r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Raw r t) : ℂ :=
  let H := p.2.2
  partialSchwartz a μ Φ (rectangularJoin (H.val * (lowerRectangle h p.2.1).val) (H⁻¹.val (Fin.last r))) *
    characterWeight d (godementExponent r s) (determinant H) *
    complexUnequalIntegrand h (ρ H⁻¹ W) V 0 p.1 * f₁ (quotientDetAbs p.1 * (δ H)⁻¹) * f₂ (δ H)

/-- The ambient kernel reads the padded Godement integrand at the representative. -/
theorem coupledHaarKernel_eq {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (a : ℂˣ) (Φ : Test r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : Raw r t) :
    coupledHaarKernel h μ d a Φ W V s f₁ f₂ p =
      paddedRestrictionKernel μ d a Φ W (padGL (Nat.succ_le_succ h.le) p.1.out)
        (lowerRectangle h p.2.1) s p.2.2 * V p.1.out * P p.1.out (0 - ((r - t : ℕ) : ℂ) / 2) *
          f₁ (quotientDetAbs p.1 * (δ p.2.2)⁻¹) * f₂ (δ p.2.2) := by
  let b := p.2.2
  let g := p.1.out
  have hrow : (padGL (Nat.succ_le_succ h.le) g * b⁻¹).val (Fin.last r) = b⁻¹.val (Fin.last r) := by
    rw [← diagonalBlocks_eq_padGL (Nat.succ_pos t) (Nat.succ_lt_succ h)]
    exact lastRow_diagonalBlocks_mul (Nat.succ_pos t) (Nat.succ_lt_succ h) g b⁻¹
  unfold coupledHaarKernel paddedRestrictionKernel complexUnequalIntegrand ArchimedeanLocal.unequalIntegrand
    ArchimedeanLocal.translateFunction
  dsimp only [b, g] at hrow
  rw [hrow]
  unfold godementExponent
  ring

private theorem measurable_coupledHaarKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test r) {ds es : List ComplexCharacterData}
    (W : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel t es (-(-a))) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    Measurable (coupledHaarKernel h μ d a Φ W.val V.val s f₁ f₂) := by
  let x := fun p : Raw r t => p.2.1
  let b := fun p : Raw r t => p.2.2
  let A := fun p : Raw r t => rectangularJoin ((b p).val * (lowerRectangle h (x p)).val)
    ((b p)⁻¹.val (Fin.last r))
  have hb : Continuous b := continuous_snd.comp continuous_snd
  have hx : Continuous x := continuous_fst.comp continuous_snd
  have hA : Continuous A := continuous_rectangularJoin.comp
    (((Units.continuous_val.comp hb).matrix_mul (Units.continuous_val.comp ((continuous_lowerRectangle h).comp hx))).prodMk
      (continuous_pi fun j => (Langlands.GeneralLinear.entry (R := ℂ) (Fin.last r) j).continuous.comp hb.inv))
  have hB : Continuous (fun p : Raw r t =>
      complexUnequalIntegrand h (ρ (b p)⁻¹ W.val) V.val 0 p.1) := by
    apply ((leftQuotient_isOpenQuotientMap (N t)).prodMap
      (IsOpenQuotientMap.id (X := Y r t × G (r + 1)))).isQuotientMap.continuous_iff.mpr
    change Continuous (fun p : G (t + 1) × (Y r t × G (r + 1)) =>
      complexUnequalIntegrand h (ρ p.2.2⁻¹ W.val) V.val 0 (Quotient.mk _ p.1))
    simp_rw [ordinaryKernel_mk h (left_translate_model W _)
      (fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g)]
    have hp := (UnequalAnalytic.continuous_padGL (Nat.succ_le_succ h.le)).comp
      (continuous_fst : Continuous (Prod.fst : G (t + 1) × (Y r t × G (r + 1)) → _))
    exact (((continuous_model W).comp (hp.mul (continuous_snd.comp continuous_snd).inv)).mul
      ((continuous_model V).comp continuous_fst)).mul ((continuous_detPower _).comp continuous_fst)
  have hχ := (continuous_characterWeight d (godementExponent r s)).comp
    (determinantContinuous.continuous.comp hb)
  have hδ : Measurable (fun p : Raw r t => δ (b p)) := ((Units.continuous_val.comp hb).matrix_det.norm.pow 2).measurable
  have hg : Measurable (fun p : Raw r t => quotientDetAbs p.1) := continuous_quotientDetAbs.measurable.comp measurable_fst
  exact (((((partialSchwartz a μ Φ).continuous.comp hA).mul hχ).mul hB).measurable.mul
    (hf₁.comp (hg.mul hδ.inv))).mul (hf₂.comp hδ)

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
  change complexNormalizedAbs (determinant (B * A) : ℂ) =
    complexNormalizedAbs (determinant z : ℂ) * complexNormalizedAbs (determinant B : ℂ)
  rw [he]
  simp only [complexNormalizedAbs, Units.val_mul, norm_mul, mul_pow]

/-- The full weighted ambient kernel is jointly integrable, without fixing either rectangle
or the ambient Haar variable. -/
def ComplexGapCoupledHaarStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t) (νY μ : AdditiveHaarMeasure ℂ)
    (κ : Measure (KU (r + 1))), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds (-a))
      (V : complexWhittakerModel t es a) (d : ComplexCharacterData) (Φ : Test r)
      (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
      (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)), HasSplitPartialTest h μ a Φ Φ₀ Ξ Ψ →
    ∀ (s : ℂ) (f₁ f₂ : ℝ → ℂ), Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
    Integrable (coupledHaarKernel h μ d a Φ W.val V.val s f₁ f₂)
      (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod (complexGeneralLinearHaar (r + 1))))

set_option maxHeartbeats 1800000 in
/-- Coupled Haar integrability for any two radial profiles bounded by independently large powers. -/
theorem complexGapCoupledHaarPowerBounds (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t)
    (νY μ : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1)))
    (hκ : κ.IsHaarMeasure) (hκinv : κ.IsInvInvariant)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds (-a))
    (V : complexWhittakerModel t es a) (d : ComplexCharacterData) (Φ : Test r)
    (Φ₀ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (hΦ : HasSplitPartialTest h μ a Φ Φ₀ Ξ Ψ) (s : ℂ) :
    ∃ α₀ γ₀ : ℝ, ∀ (f₁ f₂ : ℝ → ℂ) (α γ C₁ C₂ : ℝ),
      α₀ ≤ α → γ₀ ≤ γ → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ α) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ γ) →
      Integrable (coupledHaarKernel h μ d a Φ W.val V.val s f₁ f₂)
       (D.measure.prod ((rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)).prod (complexGeneralLinearHaar (r + 1)))) := by
  obtain ⟨α₀, γ₀, hI⟩ := complexGapCoupledPowerBounds r t h D μ νY μ κ hκ ds es a W V d Φ Φ₀ Ξ Ψ hΦ s
  refine ⟨α₀, γ₀, ?_⟩
  intro f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  let ν := μ
  let V' : complexWhittakerModel t es (-(-a)) := ⟨V.val, by simpa only [neg_neg] using V.2⟩
  let : κ.IsHaarMeasure := hκ
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : SigmaCompactSpace (Q t) := by
    let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
    have e := leftQuotient_isOpenQuotientMap (N t)
    rw [← isSigmaCompact_univ_iff, ← Set.range_eq_univ.mpr e.surjective]
    exact isSigmaCompact_range e.continuous
  let R := rightTailProductMeasure (r + 1) (t + 1) ν κ
  let X := rectangularMeasure νY (r + 1 - (t + 1)) (t + 1)
  let : X.IsAddHaarMeasure := rectangularMeasure_isAddHaar νY _ _
  let : SigmaFinite X := inferInstance
  let R₀ := ((((complexGeneralLinearHaar (t + 1)).prod (complexGeneralLinearHaar (r + 1 - (t + 1)))).prod
    (rectangularMeasure ν (t + 1) (r + 1 - (t + 1)))).prod κ)
  let : (rectangularMeasure ν (t + 1) (r + 1 - (t + 1))).IsAddHaarMeasure := rectangularMeasure_isAddHaar ν _ _
  let : SigmaFinite R₀ := inferInstance
  let : SigmaFinite R := SigmaFinite.withDensity_of_ne_top (ae_of_all R₀ fun (_ : Tail r t) => ENNReal.coe_ne_top)
  let F := coupledHaarKernel h μ d a Φ W.val V.val s f₁ f₂
  let chrom := chartOn h
  let eChart : Coords r t → Raw r t := Prod.map id (Prod.map id chrom)
  have hChart := (MeasurePreserving.id D.measure).prod ((MeasurePreserving.id X).prod
    (show MeasurePreserving chrom R (R.map chrom) from ⟨(continuous_chartOn h).measurable, rfl⟩))
  let leading := fun p : Par r t => p.2.1.1.1
  have hl : Measurable leading := by fun_prop
  let e := quotientShift (N t) leading hl
  have he := measurePreserving_quotientShift (N t) D.measure (X.prod R) D.compatible.right_invariant leading hl
  have hF := hI f₁ f₂ α γ C₁ C₂ hα hγ hm₁ hm₂ h₁ h₂
  have hpull (p : Coords r t) : F (eChart (e p)) = coupledWeightedBlockKernel h μ d a Φ W.val V.val s f₁ f₂ p := by
    let z := p.2.2.1.1.1
    let b := δ (tailOn h p.2)
    have hb : 0 < b := pow_pos (norm_pos_iff.mpr (tailOn h p.2).det_ne_zero) _
    have hz : 0 < δ z := pow_pos (norm_pos_iff.mpr z.det_ne_zero) _
    let q := (e p).1
    have hq : quotientDetAbs q = δ z * quotientDetAbs p.1 := quotientDetAbs_right p.1 z
    have hδ : δ (chrom p.2.2) = δ z * b := detAbs_chartOn h p
    have hrad : quotientDetAbs q * (δ (chrom p.2.2))⁻¹ = quotientDetAbs p.1 * b⁻¹ := by
      rw [hq, hδ]
      field_simp [hz.ne', hb.ne']
    have hBase := (blockUnfoldedKernel_shift h μ d a Φ W.val V.val
      (fun u g => complexWhittakerModel_left_equivariant W.2 u.val u.2 g)
      (fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g) s 0 (e p)).symm
    change beforeBlockKernel h μ d a Φ W.val V.val s 0 (e p) =
      blockUnfoldedKernel h μ d a Φ W.val V.val s 0 (e.symm (e p)) at hBase
    rw [MeasurableEquiv.symm_apply_apply] at hBase
    change coupledHaarKernel h μ d a Φ W.val V.val s f₁ f₂ (q, p.2.1, chrom p.2.2) = _
    rw [coupledHaarKernel_eq]
    dsimp only [chrom, chartOn]
    rw [twoBlockRestrictionKernel_chart (Nat.succ_pos t) (Nat.succ_lt_succ h)]
    change beforeBlockKernel h μ d a Φ W.val V.val s 0 (e p) *
      f₁ (quotientDetAbs q * (δ (chrom p.2.2))⁻¹) * f₂ (δ (chrom p.2.2)) = _
    rw [hBase, hrad, hδ]
    unfold blockUnfoldedKernel coupledWeightedBlockKernel weightedBlockKernel weightedOrdinary
    change _ * _ * (_ * P z (0 - (((r - t : ℕ) : ℂ) / 2))) * _ * _ * _ = _
    have hnorm : P z (0 - (((r - t : ℕ) : ℂ) / 2)) = (δ z : ℂ) ^ (-(((r - t : ℕ) : ℂ) / 2)) := by
      rw [zero_sub, ← normPower_determinant]
      rfl
    rw [hnorm]
    dsimp only [b, z]
    unfold tailOn godementExponent
    ring
  have hpre : Integrable (F ∘ eChart) (D.measure.prod (X.prod R)) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).mp
    change Integrable (fun p => F (eChart (e p))) _
    simp_rw [hpull]
    exact hF
  have hm := measurable_coupledHaarKernel h μ d a Φ W V' s f₁ f₂ hm₁ hm₂
  have hR : Integrable F (D.measure.prod (X.prod (R.map chrom))) :=
    (hChart.integrable_comp hm.aestronglyMeasurable).mp hpre
  obtain ⟨c, hc, hH⟩ := complexTwoBlockRightHaar (r + 1) (t + 1) (Nat.succ_pos t)
    (Nat.succ_lt_succ h) ν κ hκ hκinv
  change complexGeneralLinearHaar (r + 1) = c • R.map chrom at hH
  rw [hH, Measure.prod_smul_right, Measure.prod_smul_right]
  exact hR.smul_measure_nnreal

theorem complexGapCoupledHaar : ComplexGapCoupledHaarStatement := by
  intro r t h D νY μ κ hκ hκinv ds es a W V d Φ Φ₀ Ξ Ψ hΦ s f₁ f₂ hm₁ hm₂ hf₁ hf₂
  obtain ⟨α, γ, hI⟩ := complexGapCoupledHaarPowerBounds r t h D νY μ κ hκ hκinv ds es a W V d Φ Φ₀ Ξ Ψ hΦ s
  obtain ⟨C₁, h₁⟩ := hf₁ α
  obtain ⟨C₂, h₂⟩ := hf₂ γ
  exact hI f₁ f₂ α γ C₁ C₂ le_rfl le_rfl hm₁ hm₂ h₁ h₂

end Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinaryWeighted
