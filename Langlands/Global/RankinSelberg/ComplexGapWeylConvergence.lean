import Langlands.Global.RankinSelberg.ComplexGapAlternateMeasure
import Langlands.Global.RankinSelberg.ComplexGapAlternateTailWeights
import Langlands.Global.RankinSelberg.ComplexGapWeylUnfolding
import Langlands.Global.RankinSelberg.ComplexLocalParametricWeil

/-! # Absolute convergence of the Weyl-translated alternate integral -/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise SchwartzMap ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapWeylConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (det_upperUnipotent)
open Langlands.GeneralLinear (blockSumContinuous determinant determinantContinuous rankInclusion
  rankInclusionContinuous)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexSelfDualMeasure)
open ComplexGapSplitNormConvergence (alternateGapProductMeasure complexGapSplitNormConvergence)
open ComplexGapAlternateCoordinates (complexGapAlternateCoordinates firstTailColumn_consecutive
  inverseTailColumns_consecutive leadingColumns_consecutive logCongr unipotentCongr)
open ComplexGapAlternateMajorant (alternateGapNorm)
open ComplexGapAlternateMeasure (alternateToConsecutive complexGapAlternateMeasure consecutiveDensity
  consecutiveUnweightedMeasure measurable_consecutiveDensity)
open ComplexGapAlternateRepresentative (complexGapAlternateRepresentative sparseTailMatrix
  sparseTailMatrix_change)
open ComplexGapInverseTransposeTailBound (inverseTailColumns)
open ComplexGapAlternateTailWeights (complexGapAlternateTailWeights)
open ComplexGapLeadingSchwartz (matrixDecay)
open ComplexGapOrdinaryMajorant (leadingInput)
open ComplexGapRightChart (tailSize)
open ComplexGapTailEndpoints (firstTailColumn)
open ComplexGapTailExchange (SplitTailTest alternateBlockTailKernel fixedTailFactor)
open ComplexGapTriangularChart (Outer continuous_packedTail continuous_retainedMatrix outerMeasure
  retainedMatrix)
open ComplexGapUpperTail (packedTail firstRectangle)
open ComplexGapWeylUnfolding (padGL_eq_rankInclusion tailJacobian tailMatrix
  weylUnfoldedKernel weylUnfoldedKernel_mk)
open ComplexGodement (characterWeight continuous_characterWeight norm_characterWeight)
open ComplexGodementFourier (fourier)
open ComplexJacquetUnipotentMeasure (entryHaar)
open ComplexLocalIwasawa (continuous_logTorus quotientRepresentative continuous_quotientRepresentative
  mk_quotientRepresentative)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexTwoBlockHaar (rightTail)
open RealConvergenceAnalysis (norm_cexp_mul_ofReal)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

local instance gapWeylNMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance gapWeylNBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

private theorem normalizedAbs_pos {n : ℕ} (g : G n) : 0 < δ g :=
  pow_pos (norm_pos_iff.mpr g.det_ne_zero) 2

private theorem continuous_detAbs {n : ℕ} : Continuous (fun g : G n => δ g) :=
  (Units.continuous_val.matrix_det.norm).pow 2

private theorem continuous_detPower {n : ℕ} (s : ℂ) : Continuous (fun g : G n => P g s) :=
  ((Complex.continuous_ofReal.comp
    (continuous_detAbs.log fun g => (normalizedAbs_pos g).ne')).const_mul s).cexp

private theorem norm_detPower {n : ℕ} (g : G n) (s : ℂ) : ‖P g s‖ = δ g ^ s.re := by
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Real.rpow_def_of_pos (normalizedAbs_pos g)]
  rw [mul_comm]

open scoped Matrix.Norms.Operator in
private theorem continuous_whittaker {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    {W : G (r + 1) → ℂ} (hW : W ∈ complexWhittakerModel r ds a) : Continuous W :=
  (contMDiff_of_mem_complexWhittakerModel hW).continuous

variable (t q : ℕ)

local notation "Small" => (t + 1)
local notation "Order" => (t + 1 + q)
local notation "Size" => (t + 1 + q + 1)
local notation "d" => (t + 1 + q + 1 - (t + 1))
local notation "H" => G Small
local notation "Q" => LeftUnipotentQuotient t ℂ
local notation "K" => unitaryCompact ℂ Size
local notation "Row" => (Fin Size → ℂ)
local notation "J" => Fin (q + 1)
local notation "OuterTail" => Outer Small q × N (q + 1)
local notation "Coords" => (Q × ((Fin d → ℝ) × (N d × ((Fin Small → ℂ) × K)))) × (H × M d Small)
local notation "embed" => (rankInclusion (q + 1) : H →* G Size)
local notation "e" => (tailSize Small q)

private theorem rank_lt : t < Order := by omega

private theorem small_lt : Small < Size := by omega

/-- The leading test, the first physical column test, and the joint frequency test
of an alternate split kernel are Schwartz functions with the stated values. -/
def HasSchwartzTailFactors (a : ℂˣ) (T : SplitTailTest Small q)
    (Φ : 𝓢(M Size Small, ℂ)) (φ : 𝓢(Row, ℂ)) (Ξ : 𝓢(M Size d, ℂ)) : Prop :=
  T.leading = Φ ∧ T.first = φ ∧ ∀ X : M Size d,
    T.lastFrequency (fun i => X i (finCongr e (Fin.last q))) *
      (∏ j : Fin q, fourier a (T.later j) (fun i => X i (finCongr e j.castSucc))) = Ξ X

private theorem weylKernel_at (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a)
    (T : SplitTailTest Small q) (χ : ℂˣ →* ℂ) (u : ℂ) (p : OuterTail × Q)
    (g : H) (hg : Quotient.mk _ g = p.2) :
    let h := p.1.1.1.1.1
    weylUnfoldedKernel t q a T χ W.val V.val u p =
      tailJacobian t q p.1 * alternateBlockTailKernel Small q a T W.val χ (g * h) h
        (retainedMatrix Small q p.1.1) p.1.2 * (V.val (g * h) * P g u * P h u) := by
  intro h
  have hp : (p.1, Quotient.mk _ g) = p := Prod.ext rfl hg
  have hF := weylUnfoldedKernel_mk t q a ds es W V T χ u p.1 g
  rw [hp] at hF
  change weylUnfoldedKernel t q a T χ W.val V.val u p =
    (tailJacobian t q p.1 * alternateBlockTailKernel Small q a T (fun _ => 1) χ 1 h
      (retainedMatrix Small q p.1.1) p.1.2 * P h u) *
      (W.val (embed g * (tailMatrix t q p.1)⁻¹) * V.val (g * h) * P g u) at hF
  rw [hF]
  unfold alternateBlockTailKernel fixedTailFactor tailMatrix
  dsimp only
  rw [show g * h * h⁻¹ = g by exact mul_inv_cancel_right g h]
  ring

set_option maxHeartbeats 950000 in
private theorem weylKernel_product (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a)
    (T : SplitTailTest Small q) (Φ : 𝓢(M Size Small, ℂ)) (φ : 𝓢(Row, ℂ)) (Ξ : 𝓢(M Size d, ℂ))
    (hT : HasSchwartzTailFactors t q a T Φ φ Ξ)
    (χ : ℂˣ →* ℂ) (u : ℂ) (p : OuterTail × Q) (g : H) (hg : Quotient.mk _ g = p.2) :
    let S := sparseTailMatrix Small q p.1.1 p.1.2
    let h := p.1.1.1.1.1
    weylUnfoldedKernel t q a T χ W.val V.val u p =
      Φ (S.val * leadingInput (Nat.add_sub_of_le (small_lt t q).le) h.val (0 : M d Small)) *
      (φ (firstTailColumn (Nat.succ_pos t) (small_lt t q) S) * Ξ (inverseTailColumns (small_lt t q) S)) *
      W.val (embed g * S⁻¹) * V.val (g * h) * P g u *
      (χ (determinant h) * P h u) * (tailJacobian t q p.1 * χ (determinant S)) := by
  intro S h
  have hΨ :
      T.lastFrequency (Langlands.RankinSelberg.lastRow S⁻¹) *
        (∏ j : Fin q, fourier a (T.later j) (fun i => S⁻¹.val.transpose i (j.castSucc.natAdd Small))) =
          Ξ (inverseTailColumns (small_lt t q) S) := by
    have hLast : (Fin.last q).natAdd Small = Fin.last Order := Fin.ext rfl
    change T.lastFrequency (fun i => S⁻¹.val (Fin.last Order) i) * _ = _
    simpa only [inverseTailColumns_consecutive, hLast, Matrix.transpose_apply] using
      hT.2.2 (inverseTailColumns (small_lt t q) S)
  rw [weylKernel_at t q a ds es W V T χ u p g hg,
    complexGapAlternateRepresentative Small q a T ds W χ (g * h) h p.1.1 p.1.2]
  unfold fixedTailFactor
  change tailJacobian t q p.1 *
    ((T.leading (fun i j => (S * embed h).val i (j.castAdd (q + 1))) *
      T.first (fun i => S.val i ((0 : J).natAdd Small)) *
      T.lastFrequency (Langlands.RankinSelberg.lastRow S⁻¹) * W.val (embed (g * h * h⁻¹) * S⁻¹) *
      χ (determinant h) * χ (determinant S)) *
      ∏ j : Fin q, fourier a (T.later j) (fun i => S⁻¹.val.transpose i (j.castSucc.natAdd Small))) *
      (V.val (g * h) * P g u * P h u) = _
  rw [mul_inv_cancel_right, hT.1, hT.2.1, leadingColumns_consecutive Small q (small_lt t q),
    ← firstTailColumn_consecutive Small q (Nat.succ_pos t) (small_lt t q) S]
  rw [← hΨ]
  ring

private theorem continuous_sparseTail :
    Continuous (fun p : OuterTail × Q => sparseTailMatrix Small q p.1.1 p.1.2) := by
  let x (p : OuterTail × Q) := p.1.1.2
  have hX : Continuous (fun p : OuterTail × Q => firstRectangle Small q (x p)) := by
    apply continuous_matrix
    intro i j
    refine Fin.cases ?_ (fun j' => ?_) j
    · change Continuous (fun p : OuterTail × Q => p.1.1.2 i)
      exact (continuous_apply i).comp (continuous_snd.comp (continuous_fst.comp continuous_fst))
    · change Continuous (fun _ : OuterTail × Q => (0 : ℂ))
      exact continuous_const
  have hPack := (continuous_packedTail Small q).comp
    (hX.prodMk (continuous_const : Continuous (fun _ : OuterTail × Q => (1 : N (q + 1)))))
  have hY : Continuous (fun p : OuterTail × Q => p.1.1.1.1.2) := by fun_prop
  have hU : Continuous (fun p : OuterTail × Q => p.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hTail := (continuous_logTorus.comp hY).mul hU
  have hDiag : Continuous (fun p : OuterTail × Q =>
      Langlands.GeneralLinear.blockSum ((1 : H), logTorus p.1.1.1.1.2 * p.1.2.val)) :=
    (blockSumContinuous (R := ℂ)).continuous.comp (continuous_const.prodMk hTail)
  have hK : Continuous (fun p : OuterTail × Q => p.1.1.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_fst.comp
      (continuous_fst.comp continuous_fst)))
  exact (hK.mul hDiag).mul hPack

set_option maxHeartbeats 950000 in
private theorem continuous_weylKernel (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a)
    (T : SplitTailTest Small q) (Φ : 𝓢(M Size Small, ℂ)) (φ : 𝓢(Row, ℂ)) (Ξ : 𝓢(M Size d, ℂ))
    (hT : HasSchwartzTailFactors t q a T Φ φ Ξ) (d₀ : ComplexCharacterData) (z u : ℂ) :
    Continuous (weylUnfoldedKernel t q a T (characterWeight d₀ z) W.val V.val u) := by
  let S (p : OuterTail × Q) := sparseTailMatrix Small q p.1.1 p.1.2
  let g (p : OuterTail × Q) := quotientRepresentative p.2
  let h (p : OuterTail × Q) := p.1.1.1.1.1
  have hS : Continuous S := continuous_sparseTail t q
  have hg : Continuous g := continuous_quotientRepresentative.comp continuous_snd
  have hh : Continuous h := by unfold h; fun_prop
  have hW := continuous_whittaker W.2
  have hV := continuous_whittaker V.2
  have hLeading : Continuous (fun p : OuterTail × Q =>
      ((S p * embed (h p)).val : M Size Size).submatrix id (Fin.castAdd (q + 1))) := by
    have hEmbed := (rankInclusionContinuous (R := ℂ) (n := Small) (q + 1)).continuous
    have hM := Units.continuous_val.comp (hS.mul (hEmbed.comp hh))
    apply continuous_matrix
    intro i j
    exact hM.matrix_elem i (j.castAdd (q + 1))
  have hLeading' : Continuous (fun p : OuterTail × Q =>
      (S p).val * leadingInput (Nat.add_sub_of_le (small_lt t q).le) (h p).val (0 : M d Small)) := by
    simp_rw [← leadingColumns_consecutive Small q (small_lt t q)]
    exact hLeading
  have hFirst : Continuous (fun p : OuterTail × Q => firstTailColumn (Nat.succ_pos t) (small_lt t q) (S p)) := by
    simp_rw [firstTailColumn_consecutive Small q]
    apply continuous_pi
    intro i
    exact (Units.continuous_val.comp hS).matrix_elem i _
  have hFreq : Continuous (fun p : OuterTail × Q => inverseTailColumns (small_lt t q) (S p)) := by
    apply continuous_matrix
    intro i j
    unfold inverseTailColumns
    exact (Units.continuous_val.comp hS.inv).matrix_elem _ _
  have hW' : Continuous (fun p : OuterTail × Q => W.val (embed (g p) * (S p)⁻¹)) :=
    hW.comp (((rankInclusionContinuous (R := ℂ) (n := Small) (q + 1)).continuous.comp hg).mul hS.inv)
  have hV' : Continuous (fun p : OuterTail × Q => V.val (g p * h p)) := hV.comp (hg.mul hh)
  have hChar : Continuous (fun x : G Size => characterWeight d₀ z (determinant x)) :=
    (continuous_characterWeight d₀ z).comp determinantContinuous.continuous
  have hCharH : Continuous (fun x : H => characterWeight d₀ z (determinant x)) :=
    (continuous_characterWeight d₀ z).comp determinantContinuous.continuous
  have hB : Continuous (fun p : OuterTail × Q => retainedMatrix Small q p.1.1) :=
    (continuous_retainedMatrix Small q).comp (continuous_fst.comp continuous_fst)
  have hJac : Continuous (fun p : OuterTail × Q => tailJacobian t q p.1) := by
    unfold tailJacobian
    exact (Complex.continuous_ofReal.comp ((continuous_detAbs.comp hB).inv₀
      fun p => (normalizedAbs_pos (retainedMatrix Small q p.1.1)).ne')).pow q
  have hCont := ((((((Φ.continuous.comp hLeading').mul
    ((φ.continuous.comp hFirst).mul (Ξ.continuous.comp hFreq))).mul hW').mul hV').mul
    ((continuous_detPower u).comp hg)).mul
    ((hCharH.comp hh).mul ((continuous_detPower u).comp hh))).mul (hJac.mul (hChar.comp hS))
  convert hCont using 1
  funext p
  exact weylKernel_product t q a ds es W V T Φ φ Ξ hT _ u p (g p) (mk_quotientRepresentative p.2)

private theorem logCongr_roundTrip {m n : ℕ} (h : m = n) (x : Fin n → ℝ) :
    logCongr h (logCongr h.symm x) = x := by
  subst n
  rfl

private theorem unipotentCongr_roundTrip {m n : ℕ} (h : m = n) (x : N n) :
    unipotentCongr h (unipotentCongr h.symm x) = x := by
  subst n
  rfl

private theorem sum_abs_logCongr_neg {m n : ℕ} (h : m = n) (x : Fin n → ℝ) :
    ∑ i, |logCongr h.symm (-x) i| = ∑ j, |x j| := by
  subst n
  simp [logCongr]

private theorem sparseTail_at_estimateCoordinates (p : Coords) :
    let v := alternateToConsecutive t q p
    sparseTailMatrix Small q v.1.1 v.1.2 =
      rightTail (Nat.succ_pos t) (small_lt t q)
        (logTorus (-p.1.2.1) * p.1.2.2.1.val)
        (fun i j => if j.val = 0 then p.1.2.2.2.1 i else 0) p.1.2.2.2.2 := by
  intro v
  rw [complexGapAlternateCoordinates Small q (Nat.succ_pos t) (small_lt t q)]
  change rightTail _ _ (logTorus (logCongr e (logCongr (e).symm (-p.1.2.1))) *
    (unipotentCongr e (unipotentCongr (e).symm p.1.2.2.1)).val) _ _ = _
  rw [logCongr_roundTrip, unipotentCongr_roundTrip]
  rfl

private theorem sparseTail_det (p : Outer Small q) (Z : N (q + 1)) :
    determinant (retainedMatrix Small q p * (packedTail Small q 0 Z).val) =
      determinant (sparseTailMatrix Small q p Z) := by
  obtain ⟨Y, _, hY⟩ := sparseTailMatrix_change Small q p Z
  have hDet : determinant (packedTail Small q Y 1).val = 1 :=
    Units.ext (det_upperUnipotent (packedTail Small q Y 1))
  rw [hY, map_mul, hDet, mul_one]

/-- The actual alternate Weyl kernel converges absolutely when the two leading
determinant exponents are sufficiently far to the right. -/
def ComplexGapWeylConvergenceStatement : Prop :=
  ∀ (a : ℂˣ) (ds es : List ComplexCharacterData)
    (W : complexWhittakerModel Order ds (-a)) (V : complexWhittakerModel t es a)
    (D : ComplexQuotientMeasureData t) (κ : Measure K), κ.IsHaarMeasure →
    ∃ σ τ : ℝ, ∀ (d₀ : ComplexCharacterData) (z u : ℂ), σ ≤ u.re → τ ≤ (d₀.exponent + z + u).re →
      ∀ (T : SplitTailTest Small q) (Φ : 𝓢(M Size Small, ℂ)) (φ : 𝓢(Row, ℂ)) (Ξ : 𝓢(M Size d, ℂ)),
      HasSchwartzTailFactors t q a T Φ φ Ξ →
      let μ := complexSelfDualMeasure a
      Integrable (weylUnfoldedKernel t q a T (characterWeight d₀ z) W.val V.val u)
        (((outerMeasure Small q μ κ).prod (entryHaar μ (q + 1))).prod D.measure)

set_option maxHeartbeats 1650000 in
theorem complexGapWeylConvergence : ComplexGapWeylConvergenceStatement t q := by
  intro a ds es W V D κ hκ
  let μ := complexSelfDualMeasure a
  let νY : Measure (M d Small) := Measure.dirac 0
  let : IsProbabilityMeasure νY := inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : M d Small)))
  have hY : ∃ l : ℕ, Integrable (matrixDecay l) νY := ⟨0, integrable_dirac (by simp)⟩
  let Va : complexWhittakerModel t es (-(-a)) := ⟨V.val, by simpa only [neg_neg] using V.2⟩
  obtain ⟨σ, τ, hConv⟩ := complexGapSplitNormConvergence Order t (rank_lt t q) ds es (-a)
    W Va id id (fun _ => le_rfl) (fun _ => le_rfl) D μ κ hκ νY hY
  obtain ⟨hMap, hDensity⟩ := complexGapAlternateMeasure t q D μ κ hκ νY
  refine ⟨σ, τ, fun d₀ z u hu hz T Φ φ Ξ hT => ?_⟩
  dsimp only
  let χ := characterWeight d₀ z
  let F := weylUnfoldedKernel t q a T χ W.val V.val u
  let η := alternateGapProductMeasure Order t D μ κ νY
  let ν := consecutiveUnweightedMeasure t q D μ κ
  let ρ := alternateToConsecutive t q
  let w := consecutiveDensity t q
  let Fw (p : OuterTail × Q) := ((w p : ℝ) : ℂ) * F p
  let S₀ : Set Coords := {p | p.2.2 = 0}
  let I := S₀.indicator (Fw ∘ ρ)
  have hS₀ : MeasurableSet S₀ :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton _)
  have hDen : Measurable w := by
    simpa only [ENNReal.toNNReal_coe] using (measurable_consecutiveDensity t q).ennreal_toNNReal
  have hFw : Measurable Fw :=
    (Complex.measurable_ofReal.comp hDen.coe_nnreal_real).mul
      (continuous_weylKernel t q a ds es W V T Φ φ Ξ hT d₀ z u).measurable
  have hI : Measurable I := (hFw.comp hMap.measurable).indicator hS₀
  obtain ⟨C, hC, hRadius⟩ := complexGapAlternateTailWeights Small q d₀ z
  have hCompare (p : Coords) : ‖I p‖ ≤ 1 *
      alternateGapNorm (rank_lt t q) Φ φ Ξ W.val Va.val id id
        u.re (d₀.exponent + z + u).re C p.1 p.2.1 p.2.2 := by
    by_cases hp : p.2.2 = 0
    · have hmem : p ∈ S₀ := hp
      let v := ρ p
      let S := sparseTailMatrix Small q v.1.1 v.1.2
      let g := v.2.out
      let h := v.1.1.1.1.1
      let b := (d₀.exponent + z + u).re
      have hP := weylKernel_product t q a ds es W V T Φ φ Ξ hT χ u v g (Quotient.out_eq v.2)
      have hRad : ‖tailJacobian t q v.1 * χ (determinant S)‖ * (w v : ℝ) ≤
          Real.exp (C * ∑ j, |p.1.2.1 j|) := by
        have hDet := sparseTail_det t q v.1.1 v.1.2
        have hYsum : (∑ j, |v.1.1.1.1.2 j|) = ∑ j, |p.1.2.1 j| :=
          sum_abs_logCongr_neg e p.1.2.1
        simpa only [hDet, ← mul_assoc, hYsum, tailJacobian, consecutiveDensity, NNReal.coe_mul, S, χ, w] using
          hRadius v.1.1 v.1.2
      have hChar : ‖χ (determinant h)‖ = δ h ^ (d₀.exponent + z).re :=
        norm_characterWeight d₀ z (determinant h)
      let A := ‖Φ (S.val * leadingInput (Nat.add_sub_of_le (small_lt t q).le) h.val (0 : M d Small))‖ *
        ‖φ (firstTailColumn (Nat.succ_pos t) (small_lt t q) S) * Ξ (inverseTailColumns (small_lt t q) S)‖ *
        ‖W.val (embed g * S⁻¹)‖ * ‖V.val (g * h)‖ * δ g ^ u.re * δ h ^ b
      rw [show I p = Fw v from Set.indicator_of_mem hmem _]
      calc
        ‖Fw v‖ = A * (‖tailJacobian t q v.1 * χ (determinant S)‖ * (w v : ℝ)) := by
          change ‖((w v : ℝ) : ℂ) * F v‖ = _
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
          change _ * ‖weylUnfoldedKernel t q a T χ W.val V.val u v‖ = _
          change _ = Φ (S.val * leadingInput (Nat.add_sub_of_le (small_lt t q).le) h.val (0 : M d Small)) *
            (φ (firstTailColumn (Nat.succ_pos t) (small_lt t q) S) * Ξ (inverseTailColumns (small_lt t q) S)) *
            W.val (embed g * S⁻¹) * V.val (g * h) * P g u *
            (χ (determinant h) * P h u) * (tailJacobian t q v.1 * χ (determinant S)) at hP
          rw [hP]
          dsimp only [A]
          simp only [norm_mul, norm_detPower, hChar]
          have hadd : δ h ^ (d₀.exponent + z).re * δ h ^ u.re = δ h ^ b := by
            rw [← Real.rpow_add (normalizedAbs_pos h)]
            rfl
          rw [← hadd]
          ring
        _ ≤ A * Real.exp (C * ∑ j, |p.1.2.1 j|) := by
          apply mul_le_mul_of_nonneg_left hRad
          unfold A
          exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (normalizedAbs_pos g).le _))
            (Real.rpow_nonneg (normalizedAbs_pos h).le _)
        _ = _ := by
          rw [one_mul, hp]
          unfold A alternateGapNorm
          have hS : S = rightTail (Nat.succ_pos t) (small_lt t q)
              (logTorus (-p.1.2.1) * p.1.2.2.1.val)
              (fun i j => if j.val = 0 then p.1.2.2.2.1 i else 0) p.1.2.2.2.2 :=
            sparseTail_at_estimateCoordinates t q p
          have hPad : padGL (Nat.succ_le_succ (rank_lt t q).le) g = embed g :=
            padGL_eq_rankInclusion (m := Small) (n := q + 1) g
          dsimp only
          rw [hS, ← hPad]
          rfl
    · rw [show I p = 0 from Set.indicator_of_notMem (show p ∉ S₀ from hp) _, norm_zero]
      unfold alternateGapNorm complexNormalizedAbs
      positivity
  have hIntI := hConv u.re (d₀.exponent + z + u).re C hu hz hC Φ φ Ξ 1 zero_le_one I
    hI.aestronglyMeasurable hCompare
  have hSupport : ∀ᵐ p ∂η, p ∈ S₀ := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem hS₀).mpr
    apply ae_of_all
    intro v
    apply (Measure.ae_prod_iff_ae_ae
      (measurable_snd (measurableSet_singleton (0 : M d Small)))).mpr
    exact ae_of_all _ fun _ => by simp [νY]
  have hIntComp : Integrable (Fw ∘ ρ) η :=
    hIntI.congr (hSupport.mono fun p hp => Set.indicator_of_mem hp _)
  have hFwI : Integrable Fw ν := by
    have hAtMap := (integrable_map_measure hFw.aestronglyMeasurable hMap.measurable.aemeasurable).mpr hIntComp
    rwa [hMap.map_eq] at hAtMap
  rw [hDensity]
  apply (integrable_withDensity_iff_integrable_coe_smul hDen).mpr
  simpa only [Complex.real_smul] using hFwI

end Langlands.Global.RankinSelbergGlobal.ComplexGapWeylConvergence
