import Langlands.Global.RankinSelberg.RealGapNormalizationColumns

/-! # Joint convergence on the real determinant-one gap chart -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapNormalizedWeighted

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose_coe rankInclusion)
open Langlands.HarmonicAnalysis (rowMeasure)
open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.QuotientIntegration (descend rightTranslate rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient det_rankInclusion unipotent_det)
open ArchimedeanLocal (RealQuotientMeasureData realSelfDualMeasure realNormalizedAbs realUnequalIntegrand)
open ArchimedeanMellinPair (RapidDecay)
open RealGapAlternateConvergence (alternateGapMeasure)
open RealGapAlternateHaarDecay (normalizedDet_retained)
open RealGapAlternateWeighted (leadingSide weightedAlternateKernel realGapAlternatePowerBounds ordinaryKernel_mk
  left_translate leftCharacter_of_mem)
open RealGapColumnFourier (triangularFourier)
open RealGapLeadingSchwartz (leadingStack matrixDecay)
open RealGapNormalizationColumns (leadingSide_involutive realGapNormalizationColumns)
open RealGapNormalizationShear (normalizationShear normalizationShear_apply outerChange outerChange_apply
  continuous_leadingScalar realGapNormalizationShear)
open RealGapTriangularChart (Outer retainedMatrix outerMeasure diagonalWeightMeasure)
open RealGapUnitDeterminant (leadingScalar unitRetained normalizedAbs_unitRetained normalizationWeight
  normalizationWeight_eq unitOuterMeasure)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealUnequalFamily (HasLeftCharacter)
open RealUnequalMellinReduction (quotientDetAbs)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "Size" => fun t q => t + 1 + q + 1
local notation "Rect" => fun t q => Mat (q + 1) (t + 1)
local notation "Par" => fun t q => Rect t q × (Outer (t + 1) q × U (q + 1))
local notation "Coords" => fun t q => Q t × Par t q
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "ρ" => ArchimedeanLocal.translateFunction

local instance gapNormalizedWeightMatrixSecondCountable (m n : ℕ) :
    SecondCountableTopology (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
local instance gapNormalizedWeightGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapNormalizedWeightGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapNormalizedWeightGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapNormalizedWeightGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n ℝ) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapNormalizedWeightUMeasurable (n : ℕ) : MeasurableSpace (U n) := borel _
local instance gapNormalizedWeightUBorel (n : ℕ) : BorelSpace (U n) := ⟨rfl⟩
local instance gapNormalizedWeightQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _


private theorem gap_lt (t q : ℕ) : t < t + 1 + q := by omega

private theorem detAbs_pos {n : ℕ} (g : G n) : 0 < δ g := abs_pos.mpr g.det_ne_zero

private theorem detAbs_mul {n : ℕ} (g h : G n) : δ (g * h) = δ g * δ h := by
  simp only [Units.val_mul, Matrix.det_mul, realNormalizedAbs, abs_mul]

private theorem detPower_real_mul {n : ℕ} (g h : G n) (s : ℂ) : P (g * h) s = P g s * P h s := by
  unfold ArchimedeanLocal.detPower
  have hnorm : realNormalizedAbs (g * h).val.det = realNormalizedAbs g.val.det * realNormalizedAbs h.val.det :=
    detAbs_mul g h
  rw [hnorm, Real.log_mul (detAbs_pos g).ne' (detAbs_pos h).ne', Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem detAbs_inv {n : ℕ} (g : G n) : δ g⁻¹ = (δ g)⁻¹ := by
  have hg := (detAbs_pos g).ne'
  have h := detAbs_mul g g⁻¹
  rw [mul_inv_cancel, show δ (1 : G n) = 1 by simp [realNormalizedAbs]] at h
  exact mul_left_cancel₀ hg (h.symm.trans (mul_inv_cancel₀ hg).symm)

private theorem detAbs_leadingScalar {t q : ℕ} (p : Outer (t + 1) q) :
    δ (leadingScalar (t + 1) q p.1.1.2) = Real.exp ((-1 : ℝ) * ∑ i, p.1.1.2 i) := by
  have h := normalizedAbs_unitRetained (t + 1) q (Nat.succ_pos _) p
  change δ (retainedMatrix (t + 1) q p * rankInclusion (q + 1) (leadingScalar (t + 1) q p.1.1.2)) = 1 at h
  rw [detAbs_mul, normalizedDet_retained] at h
  change Real.exp (∑ i, p.1.1.2 i) *
    realNormalizedAbs (rankInclusion (q + 1) (leadingScalar (t + 1) q p.1.1.2)).val.det = 1 at h
  have hS := congrArg realNormalizedAbs (det_rankInclusion (q + 1) (leadingScalar (t + 1) q p.1.1.2))
  rw [hS] at h
  change realNormalizedAbs (leadingScalar (t + 1) q p.1.1.2).val.det = _
  apply mul_left_cancel₀ (Real.exp_ne_zero (∑ i, p.1.1.2 i))
  rw [h, ← Real.exp_add, neg_one_mul, add_neg_cancel, Real.exp_zero]

private def sideScale (dual : Bool) : ℝ := if dual then -1 else 1

private theorem detAbs_shearedSide {t q : ℕ} (dual : Bool) (p : Outer (t + 1) q) :
    δ (leadingSide dual (outerChange (t + 1) q dual p).1.1.1) =
      Real.exp (sideScale dual * ∑ i, p.1.1.2 i) * δ p.1.1.1 := by
  rw [outerChange_apply]
  change δ (leadingSide dual ((leadingScalar (t + 1) q p.1.1.2)⁻¹ * leadingSide dual p.1.1.1)) = _
  rw [RealGapNormalizationColumns.leadingSide_mul, leadingSide_involutive, detAbs_mul]
  congr 1
  cases dual
  · change δ (leadingScalar (t + 1) q p.1.1.2)⁻¹ = Real.exp (1 * ∑ i, p.1.1.2 i)
    rw [detAbs_inv, detAbs_leadingScalar p, ← Real.exp_neg, neg_mul, neg_neg]
  · change realNormalizedAbs (Langlands.GeneralLinear.inverseTranspose _ ℝ
        (leadingScalar (t + 1) q p.1.1.2)⁻¹).val.det = _
    rw [inverseTranspose_coe, Matrix.det_transpose, inv_inv]
    exact detAbs_leadingScalar p

/-- The quotient determinant can be evaluated at any representative. -/
theorem quotientDetAbs_mk {t : ℕ} (g : G (t + 1)) : quotientDetAbs (Quotient.mk _ g : Q t) = δ g := by
  let f : Q t → ℝ := descend (U (t + 1)) (fun g => δ g) fun u x => by
    change realNormalizedAbs (u.val.val * x.val).det = _
    rw [Matrix.det_mul, unipotent_det, one_mul]
  have hf (x : Q t) : f x = quotientDetAbs x := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  rw [← hf]
  rfl

/-- Right translation multiplies the normalized quotient determinant by the translating determinant. -/
theorem quotientDetAbs_right {t : ℕ} (x : Q t) (S : G (t + 1)) :
    quotientDetAbs (rightTranslate (U (t + 1)) S x) = δ S * quotientDetAbs x := by
  induction x using Quotient.inductionOn with
  | h g => rw [rightTranslate_mk, quotientDetAbs_mk, quotientDetAbs_mk, detAbs_mul, mul_comm]

/-- Padding in consecutive coordinates is the leading block inclusion. -/
theorem padGL_eq_rankInclusion (k q : ℕ) (g : G k) :
    padGL (show k ≤ k + (q + 1) by omega) g = rankInclusion (q + 1) g := by
  apply Units.ext
  ext i j
  rw [Unfolding.padGL_apply]
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · simp [rankInclusion, i₀.isLt, j₀.isLt]
  · simp [rankInclusion, i₀.isLt]
  · have hij : i₁.natAdd k ≠ j₀.castAdd (q + 1) := by
      intro h
      have he := congrArg Fin.val h
      change k + i₁.val = j₀.val at he
      omega
    simp [rankInclusion, hij]
  · simp [rankInclusion, Matrix.one_apply, Fin.natAdd_inj]

private theorem shiftedProduct {t q : ℕ} {a : ℝˣ} {W : G (Size t q) → ℂ} {V : G (t + 1) → ℂ}
    (hW : HasLeftCharacter (-a) W) (hV : HasLeftCharacter (-(-a)) V)
    (s : ℂ) (B : G (Size t q)) (S h : G (t + 1)) (x : Q t) :
    realUnequalIntegrand (gap_lt t q) (ρ (B * rankInclusion (q + 1) S)⁻¹ W) (ρ (S⁻¹ * h) V) s
        (rightTranslate (U (t + 1)) S x) =
      realUnequalIntegrand (gap_lt t q) (ρ B⁻¹ W) (ρ h V) s x * P S (s - (((t + 1 + q) - t : ℕ) : ℂ) / 2) := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk, ordinaryKernel_mk _ (left_translate hW _) (left_translate hV _),
      ordinaryKernel_mk _ (left_translate hW _) (left_translate hV _)]
    have hp (y : G (t + 1)) : padGL (Nat.succ_le_succ (gap_lt t q).le) y = rankInclusion (q + 1) y :=
      padGL_eq_rankInclusion (t + 1) q y
    simp only [ArchimedeanLocal.translateFunction, hp,
      map_mul, mul_inv_rev, mul_assoc, mul_inv_cancel_left, detPower_real_mul]

/-- The two rapid weights on the normalized chart depend only on the two determinant variables. -/
def normalizedWeightedKernel {t q : ℕ} (dual : Bool) (a : ℝˣ) (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ))
    (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ)) (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
    (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ) (s : ℂ)
    (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ) (v : Coords t q) : ℂ :=
  let p := v.2.2.1
  let h := p.1.1.1
  let B := unitRetained (t + 1) q p
  Φ₀ ((leadingSide dual B).val * leadingStack (leadingSide dual h).val v.2.1) *
    Φ (fun i => B.val i ((0 : Fin (q + 1)).natAdd (t + 1))) * Ψ (Langlands.RankinSelberg.lastRow B⁻¹) *
    triangularFourier (t + 1) q a B Ξ v.2.2.2 *
    realUnequalIntegrand (gap_lt t q) (ρ B⁻¹ W) (ρ h V) s v.1 *
    f₁ (quotientDetAbs v.1) * f₂ (δ (leadingSide dual h)) * w p

/-- On the normalized chart the outer Haar factor includes the Jacobian of the complementary rectangle. -/
def normalizedGapMeasure (t q : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (νY : Measure (Rect t q)) (η₁ : Measure (G (t + 1))) (κ : Measure (KU (Size t q))) :
    Measure (Coords t q) :=
  let μ := realSelfDualMeasure a
  D.measure.prod (νY.prod ((unitOuterMeasure (t + 1) q μ η₁ κ).prod (entryHaar μ (q + 1))))

private def densityOuter {t q : ℕ} (p : Outer (t + 1) q) : ℝ≥0 := normalizationWeight (t + 1) q p.1.1.2

private theorem measurable_densityOuter {t q : ℕ} : Measurable (densityOuter (t := t) (q := q)) := by
  have hLog : Continuous (fun p : Outer (t + 1) q => ∑ i, p.1.1.2 i) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp (continuous_snd.comp (continuous_fst.comp continuous_fst))
  apply Measurable.subtype_mk
  change Measurable (fun p : Outer (t + 1) q => (densityOuter p : ℝ))
  simp_rw [densityOuter, normalizationWeight_eq _ _ (Nat.succ_pos _)]
  exact (Real.continuous_exp.comp (continuous_const.mul hLog)).measurable

private theorem normalizedGapMeasure_eq {t q : ℕ} (a : ℝˣ) (D : RealQuotientMeasureData t)
    (νY : Measure (Rect t q)) (η₁ : Measure (G (t + 1))) (κ : Measure (KU (Size t q)))
    [η₁.IsHaarMeasure] [κ.IsHaarMeasure] [SigmaFinite νY] :
    normalizedGapMeasure t q a D νY η₁ κ =
      (alternateGapMeasure t q a D νY η₁ κ).withDensity (fun v => (densityOuter v.2.2.1 : ℝ≥0∞)) := by
  let μ := realSelfDualMeasure a
  let A := outerMeasure (t + 1) q μ η₁ κ
  let Z := entryHaar μ (q + 1)
  let θ := fun p : Outer (t + 1) q => (densityOuter p : ℝ≥0∞)
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite κ := inferInstance
  let : SigmaFinite A := inferInstanceAs (SigmaFinite
    (((η₁.prod (diagonalWeightMeasure (t + 1) q)).prod κ).prod (rowMeasure μ (t + 1))))
  let : SigmaFinite Z := entryHaar_sigmaFinite μ _
  have hθ : Measurable θ := measurable_densityOuter.coe_nnreal_ennreal
  have hθ' : Measurable (fun v : Outer (t + 1) q × U (q + 1) => θ v.1) := hθ.comp measurable_fst
  have hθ'' : Measurable (fun v : Par t q => θ v.2.1) := hθ'.comp measurable_snd
  change D.measure.prod (νY.prod ((A.withDensity θ).prod Z)) = (D.measure.prod (νY.prod (A.prod Z))).withDensity _
  rw [prod_withDensity_left hθ, prod_withDensity_right hθ', prod_withDensity_right hθ'']

private def spectralShift (t q : ℕ) (s : ℂ) : ℂ := s - (((t + 1 + q) - t : ℕ) : ℂ) / 2

private def shearedMultiplier {t q : ℕ} (dual : Bool) (s : ℂ) (w : Outer (t + 1) q → ℂ) (p : Outer (t + 1) q) : ℂ :=
  (densityOuter p : ℝ) • (P (leadingScalar (t + 1) q p.1.1.2) (spectralShift t q s) * w (outerChange (t + 1) q dual p))

private theorem measurable_shearedMultiplier {t q : ℕ} (dual : Bool) (s : ℂ) {w : Outer (t + 1) q → ℂ}
    (hw : Measurable w) : Measurable (shearedMultiplier dual s w) := by
  have hS : Continuous fun p : Outer (t + 1) q => leadingScalar (t + 1) q p.1.1.2 :=
    (continuous_leadingScalar _ _).comp (continuous_snd.comp (continuous_fst.comp continuous_fst))
  have hδ : Continuous fun p : Outer (t + 1) q => δ (leadingScalar (t + 1) q p.1.1.2) :=
    (Units.continuous_val.comp hS).matrix_det.abs
  have hP : Continuous fun p : Outer (t + 1) q => P (leadingScalar (t + 1) q p.1.1.2) (spectralShift t q s) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (hδ.log fun _ => (detAbs_pos _).ne')))
  exact measurable_densityOuter.coe_nnreal_real.smul (hP.measurable.mul (hw.comp (outerChange _ _ dual).measurable))

private theorem exp_mul_logSum_le {t q : ℕ} (x : ℝ) (p : Outer (t + 1) q) :
    x * (∑ i, p.1.1.2 i) ≤ |x| * ∑ i, |p.1.1.2 i| := calc
  _ ≤ |x| * |∑ i, p.1.1.2 i| := by rw [← abs_mul]; exact le_abs_self _
  _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)

private def logCoefficient (t q : ℕ) (dual : Bool) (s : ℂ) (β : ℝ) : ℝ :=
  -(q : ℝ) + (spectralShift t q s).re * (-1) + β * sideScale dual

private theorem norm_shearedMultiplier {t q : ℕ} (dual : Bool) (s : ℂ) {w : Outer (t + 1) q → ℂ}
    (C β b : ℝ) (hC : 0 ≤ C)
    (hw : ∀ p, ‖w p‖ ≤ C * δ (leadingSide dual p.1.1.1) ^ β * Real.exp (b * ∑ i, |p.1.1.2 i|))
    (p : Outer (t + 1) q) :
    ‖shearedMultiplier dual s w p‖ ≤ C * δ p.1.1.1 ^ β *
      Real.exp ((b + |logCoefficient t q dual s β|) * ∑ i, |p.1.1.2 i|) := by
  let z := p.1.1.1
  let y := ∑ i, p.1.1.2 i
  let A := ∑ i, |p.1.1.2 i|
  let S := leadingScalar (t + 1) q p.1.1.2
  let ω := spectralShift t q s
  have hz := detAbs_pos z
  have hP : ‖P S ω‖ = Real.exp ((ω.re * (-1)) * y) := by
    unfold ArchimedeanLocal.detPower
    rw [RealConvergenceAnalysis.norm_cexp_mul_ofReal]
    change Real.exp (ω.re * Real.log (δ S)) = _
    rw [detAbs_leadingScalar p, Real.log_exp, mul_assoc]
  have hW := hw (outerChange (t + 1) q dual p)
  rw [detAbs_shearedSide dual p] at hW
  change ‖w (outerChange (t + 1) q dual p)‖ ≤ C * (Real.exp (sideScale dual * y) * δ z) ^ β * Real.exp (b * A) at hW
  rw [Real.mul_rpow (Real.exp_nonneg _) hz.le, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hW
  unfold shearedMultiplier
  rw [norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg _), norm_mul, hP, densityOuter,
    normalizationWeight_eq _ _ (Nat.succ_pos _)]
  calc
    _ ≤ Real.exp (-(q : ℝ) * y) * (Real.exp ((ω.re * (-1)) * y) *
        (C * (Real.exp (sideScale dual * y * β) * δ z ^ β) * Real.exp (b * A))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = C * δ z ^ β * Real.exp (logCoefficient t q dual s β * y + b * A) := by
      rw [show logCoefficient t q dual s β * y + b * A =
        -(q : ℝ) * y + (ω.re * (-1)) * y + sideScale dual * y * β + b * A by
        unfold logCoefficient ω; ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC (Real.rpow_nonneg hz.le _))
      rw [add_mul]
      have hL := exp_mul_logSum_le (logCoefficient t q dual s β) p
      change logCoefficient t q dual s β * y ≤ |logCoefficient t q dual s β| * A at hL
      change logCoefficient t q dual s β * y + b * A ≤ b * A + |logCoefficient t q dual s β| * A
      linarith

set_option maxHeartbeats 1000000 in
private theorem normalizedWeightedKernel_shear {t q : ℕ} (dual : Bool) (a : ℝˣ)
    {W : G (Size t q) → ℂ} {V : G (t + 1) → ℂ}
    (hW : HasLeftCharacter (-a) W) (hV : HasLeftCharacter (-(-a)) V)
    (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ)) (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ))
    (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ)) (s : ℂ) (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ)
    (v : Coords t q) :
    (let v' := normalizationShear t q dual v
     (densityOuter v'.2.2.1 : ℝ) • normalizedWeightedKernel dual a Φ₀ Φ Ψ Ξ W V s f₁ f₂ w v') =
      weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ W V s (-1) (sideScale dual) f₁ f₂ (shearedMultiplier dual s w) v := by
  let p := v.2.2.1
  let S := leadingScalar (t + 1) q p.1.1.2
  let h := leadingSide dual p.1.1.1
  let B := retainedMatrix (t + 1) q p
  let C := B * rankInclusion (q + 1) S
  let p' := outerChange (t + 1) q dual p
  let x' := rightTranslate (U (t + 1)) S v.1
  obtain ⟨hLead, hTail, hFirst, hLast⟩ := realGapNormalizationColumns (t + 1) q dual a B S (S⁻¹ * h) v.2.1 Ξ v.2.2.2
  rw [mul_inv_cancel_left, leadingSide_involutive] at hLead
  have hL : (leadingSide dual C).val * leadingStack (leadingSide dual p'.1.1.1).val v.2.1 =
      (leadingSide dual B).val * leadingStack p.1.1.1.val v.2.1 := hLead
  have hDet : quotientDetAbs x' = Real.exp ((-1 : ℝ) * ∑ i, p.1.1.2 i) * quotientDetAbs v.1 := by
    change quotientDetAbs (rightTranslate (U (t + 1)) S v.1) = _
    rw [quotientDetAbs_right, detAbs_leadingScalar p]
  have hProd := shiftedProduct hW hV s B S h v.1
  change (densityOuter p' : ℝ) •
    (Φ₀ ((leadingSide dual C).val * leadingStack (leadingSide dual p'.1.1.1).val v.2.1) *
      Φ (fun i => C.val i ((0 : Fin (q + 1)).natAdd (t + 1))) * Ψ (Langlands.RankinSelberg.lastRow C⁻¹) *
      triangularFourier (t + 1) q a C Ξ v.2.2.2 *
      realUnequalIntegrand (gap_lt t q) (ρ C⁻¹ W) (ρ (S⁻¹ * h) V) s x' *
      f₁ (quotientDetAbs x') * f₂ (δ (leadingSide dual p'.1.1.1)) * w p') = _
  rw [hL, hFirst, hLast, hTail, hProd, hDet, detAbs_shearedSide dual p]
  have hθ : densityOuter p' = densityOuter p := rfl
  rw [hθ]
  simp only [weightedAlternateKernel, shearedMultiplier, Algebra.smul_def]
  let K := Φ₀ ((leadingSide dual B).val * leadingStack p.1.1.1.val v.2.1) *
    Φ (fun i => B.val i ((0 : Fin (q + 1)).natAdd (t + 1))) * Ψ (Langlands.RankinSelberg.lastRow B⁻¹) *
    triangularFourier (t + 1) q a B Ξ v.2.2.2
  let J := realUnequalIntegrand (gap_lt t q) (ρ B⁻¹ W) (ρ h V) s v.1
  let u₁ := f₁ (Real.exp ((-1 : ℝ) * ∑ i, p.1.1.2 i) * quotientDetAbs v.1)
  let u₂ := f₂ (Real.exp (sideScale dual * ∑ i, p.1.1.2 i) * δ p.1.1.1)
  let d := (algebraMap ℝ ℂ) (densityOuter p : ℝ)
  let z := P S (spectralShift t q s)
  change d * (K * (J * z) * u₁ * u₂ * w p') = K * J * u₁ * u₂ * (d * (z * w p'))
  ring

/-- Independent rapidly decaying determinant weights give joint absolute convergence on the normalized chart. -/
def RealGapNormalizedWeightedStatement : Prop :=
  ∀ (t q : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData t) (νY : Measure (Rect t q))
    (η₁ : Measure (G (t + 1))) (κ : Measure (KU (Size t q))),
    η₁.IsHaarMeasure → κ.IsHaarMeasure → SigmaFinite νY → ∀ l : ℕ, Integrable (matrixDecay l) νY →
    ∀ (dual : Bool) (ds es : List RealBlock) (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ),
      W ∈ realUniformWhittakerModel (t + 1 + q) ds (-a) → V ∈ realUniformWhittakerModel t es a →
    ∀ (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ))
      (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ)) (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
      (s : ℂ) (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ) (C β b : ℝ),
      0 ≤ C → 0 ≤ b → Measurable w → Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
      (∀ p, ‖w p‖ ≤ C * δ (leadingSide dual p.1.1.1) ^ β * Real.exp (b * ∑ i, |p.1.1.2 i|)) →
      Integrable (normalizedWeightedKernel dual a Φ₀ Φ Ψ Ξ W V s f₁ f₂ w)
        (normalizedGapMeasure t q a D νY η₁ κ)

set_option maxHeartbeats 1000000 in
/-- The original normalized chart accepts two independent sufficiently large power bounds. -/
theorem realGapNormalizedPowerBounds (t q : ℕ) (a : ℝˣ)
    (D : RealQuotientMeasureData t) (νY : Measure (Rect t q)) (η₁ : Measure (G (t + 1)))
    (κ : Measure (KU (Size t q))) (hη₁ : η₁.IsHaarMeasure)
    (hκ : κ.IsHaarMeasure) (hνY : SigmaFinite νY) (l : ℕ) (hY : Integrable (matrixDecay l) νY)
    (ds es : List RealBlock) (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ)
    (hWm : W ∈ realUniformWhittakerModel (t + 1 + q) ds (-a))
    (hVm : V ∈ realUniformWhittakerModel t es a) (s : ℂ) (β : ℝ) :
    ∃ u v : ℝ, ∀ (dual : Bool) (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ))
      (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ)) (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
      (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ) (C b p₁ p₂ C₁ C₂ : ℝ),
      0 ≤ C → 0 ≤ b → u ≤ p₁ → v ≤ p₂ → Measurable w → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ p₁) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ p₂) →
      (∀ p, ‖w p‖ ≤ C * δ (leadingSide dual p.1.1.1) ^ β * Real.exp (b * ∑ i, |p.1.1.2 i|)) →
      Integrable (normalizedWeightedKernel dual a Φ₀ Φ Ψ Ξ W V s f₁ f₂ w)
        (normalizedGapMeasure t q a D νY η₁ κ) := by
  obtain ⟨u, v, hI⟩ := realGapAlternatePowerBounds t q a D νY η₁ κ hη₁ hκ hνY l hY ds es W V hWm hVm s β
  refine ⟨u, v, ?_⟩
  intro dual Φ₀ Φ Ψ Ξ f₁ f₂ w C b p₁ p₂ C₁ C₂ hC hb hp₁ hp₂ hw hm₁ hm₂ h₁ h₂ hW
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite νY := hνY
  have hVl : HasLeftCharacter (-(-a)) V := by
    rw [neg_neg]
    exact leftCharacter_of_mem hVm
  let F := normalizedWeightedKernel dual a Φ₀ Φ Ψ Ξ W V s f₁ f₂ w
  change Integrable F _
  rw [normalizedGapMeasure_eq]
  have hθ : Measurable (fun v : Coords t q => densityOuter v.2.2.1) :=
    measurable_densityOuter.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  apply (integrable_withDensity_iff_integrable_coe_smul hθ).mpr
  let e := normalizationShear t q dual
  have he := realGapNormalizationShear t q a D νY η₁ κ hη₁ hκ hνY dual
  apply (he.integrable_comp_emb e.measurableEmbedding).mp
  have hEq : (fun v : Coords t q => (densityOuter v.2.2.1 : ℝ) • F v) ∘ e =
      weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ W V s (-1) (sideScale dual) f₁ f₂ (shearedMultiplier dual s w) :=
    funext (normalizedWeightedKernel_shear dual a (leftCharacter_of_mem hWm) hVl Φ₀ Φ Ψ Ξ s f₁ f₂ w)
  rw [hEq]
  exact hI dual Φ₀ Φ Ψ Ξ (-1) (sideScale dual) f₁ f₂ (shearedMultiplier dual s w)
    C (b + |logCoefficient t q dual s β|) p₁ p₂ C₁ C₂ hC (by positivity) hp₁ hp₂
    (measurable_shearedMultiplier dual s hw) hm₁ hm₂ h₁ h₂ (norm_shearedMultiplier dual s C β b hC hW)

theorem realGapNormalizedWeighted : RealGapNormalizedWeightedStatement := by
  intro t q a D νY η₁ κ hη₁ hκ hνY l hY dual ds es W V hWm hVm Φ₀ Φ Ψ Ξ s f₁ f₂ w C β b hC hb hw hm₁ hm₂
    hf₁ hf₂ hW
  obtain ⟨u, v, hI⟩ := realGapNormalizedPowerBounds t q a D νY η₁ κ hη₁ hκ hνY l hY ds es W V hWm hVm s β
  obtain ⟨C₁, h₁⟩ := hf₁ u
  obtain ⟨C₂, h₂⟩ := hf₂ v
  exact hI dual Φ₀ Φ Ψ Ξ f₁ f₂ w C b u v C₁ C₂ hC hb le_rfl le_rfl hw hm₁ hm₂ h₁ h₂ hW

end Langlands.Global.RankinSelbergGlobal.RealGapNormalizedWeighted
