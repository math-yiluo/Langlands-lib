import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RealLocalWhittakerChangeCharacter
import Langlands.Global.RankinSelberg.RealLocalQuotientChange
import Langlands.Global.RankinSelberg.RealLocalAdjacentUnfolding
import Langlands.Global.RankinSelberg.RealUnequalOrdinaryFamily

/-! # Additive character transport for real ordinary Rankin–Selberg tests -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.RankinSelbergGlobal.RealCharacterChange

open ArchimedeanLocal Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val diagonalUnits_mul_mul_apply)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open RealEqualConvergence (realWhittakerCharacter_mul_neg)
open RealJacquet (realDetPower_mul)
open RealUnequalFamily (HasLeftCharacter)
open UnipotentConjugationModulus (conjugation)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

/-- The rank-`r + 1` leading block of the diagonal with entries `a^q, …, 1`,
where `r ≤ q`. -/
def leadingCharacterDiagonal (r q : ℕ) (a : ℝˣ) : G r :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) fun i : Fin (r + 1) => a ^ (q - i.val)

private theorem leadingCharacterDiagonal_character {r q : ℕ} (h : r ≤ q) (a b : ℝˣ) (u : G r) :
    realWhittakerCharacter b (leadingCharacterDiagonal r q a * u *
      (leadingCharacterDiagonal r q a)⁻¹) = realWhittakerCharacter (b * a) u := by
  have hentry (i : Fin r) : (leadingCharacterDiagonal r q a * u *
      (leadingCharacterDiagonal r q a)⁻¹) i.castSucc i.succ = (a : ℝ) * u i.castSucc i.succ := by
    have hi : q - i.castSucc.val = q - i.succ.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    have hpow : (a ^ (q - i.castSucc.val) * (a ^ (q - i.succ.val))⁻¹ : ℝˣ) = a := by
      rw [hi, pow_succ', mul_assoc, mul_inv_cancel, mul_one]
    unfold leadingCharacterDiagonal
    rw [← map_inv, diagonalUnits_mul_mul_apply, Pi.inv_apply]
    calc
      _ = (((a ^ (q - i.castSucc.val) * (a ^ (q - i.succ.val))⁻¹ : ℝˣ) : ℝ)) *
          u i.castSucc i.succ := by simp only [Units.val_mul]; ring
      _ = _ := by rw [hpow]
  unfold realWhittakerCharacter
  simp only [hentry, ← Finset.mul_sum]
  change ((realScaledCharacter b ((a : ℝ) * ∑ i : Fin r, u i.castSucc i.succ) : Circle) : ℂ) =
    ((realScaledCharacter (b * a) (∑ i : Fin r, u i.castSucc i.succ) : Circle) : ℂ)
  rw [realScaledCharacter_apply, realScaledCharacter_apply, Units.val_mul, mul_assoc]

private theorem leftTranslate_intertwiner_leading {r q : ℕ} (h : r ≤ q) {ds : List RealBlock}
    (a b : ℝˣ) {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G r → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds b B) :
    IsRealWhittakerIntertwiner r ds (b * a) ((leftTranslate (leadingCharacterDiagonal r q a)).comp B) := by
  let m := leadingCharacterDiagonal r q a
  refine ⟨?_, fun f => (hB.2.1 f).comp contMDiff_mul_left, ?_, ?_, ?_⟩
  · intro f u hu g
    change B f (m * (u * g)) = realWhittakerCharacter (b * a) u * B f (m * g)
    have hu' : m * u * m⁻¹ ∈ GeneralLinear.upperUnipotent (r + 1) ℝ :=
      diagonal_conj_mem (fun i : Fin (r + 1) => a ^ (q - i.val)) u hu
    have hprod : m * (u * g) = (m * u * m⁻¹) * (m * g) := by
      rw [mul_assoc (m * u), inv_mul_cancel_left, mul_assoc]
    rw [hprod, hB.1 f _ hu']
    exact congrArg (· * B f (m * g)) (leadingCharacterDiagonal_character h a b u)
  · intro f
    obtain ⟨C, k, hC, hf⟩ := RealLocalWhittaker.HasPolynomialGrowth.of_bound (hB.2.2.1 f)
    refine ⟨C * realMatrixHeight m ^ k, k, fun g => ?_⟩
    change ‖B f (m * g)‖ ≤ _
    calc
      _ ≤ C * realMatrixHeight (m * g) ^ k := hf _
      _ ≤ C * (realMatrixHeight m * realMatrixHeight g) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (RealPlaceRestriction.realMatrixHeight_nonneg _) (realMatrixHeight_mul_le _ _) _) hC
      _ = _ := by rw [mul_pow, mul_assoc]
  · intro k f f' hf
    funext g
    change B f' (m * g) = B f (m * (g * k.val))
    rw [hB.2.2.2.1 k f f' hf]
    change B f ((m * g) * k.val) = _
    rw [mul_assoc]
  · intro X f f' hf
    funext g
    change B f' (m * g) = rightDerivative (matrixModel ℝ (r + 1)) X (fun y => B f (m * y)) g
    rw [hB.2.2.2.2 X f f' hf]
    unfold rightDerivative
    have he : (fun y : G r => B f ((m * g) * y)) = (fun y : G r => B f (m * (g * y))) :=
      funext fun y => by rw [mul_assoc]
    exact congrArg (fun F : G r → ℂ =>
      mfderiv (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) F (1 : G r) X) he

/-- Left multiplication by the leading character diagonal preserves the coefficient
model and multiplies its additive scale by `a`. -/
theorem leftTranslate_leading_mem_model {r q : ℕ} (h : r ≤ q) {ds : List RealBlock}
    {a b : ℝˣ} {W : G r → ℂ} (hW : W ∈ realWhittakerModel r ds b) :
    leftTranslate (leadingCharacterDiagonal r q a) W ∈ realWhittakerModel r ds (b * a) := by
  let L := leftTranslate (leadingCharacterDiagonal r q a)
  have hle : realWhittakerModel r ds b ≤ (realWhittakerModel r ds (b * a)).comap L := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.mem_iSup_of_mem (L.comp B)
      (Submodule.mem_iSup_of_mem (leftTranslate_intertwiner_leading h a b hB) ⟨f, rfl⟩)
  exact hle hW

/-- A nonzero coefficient model stays nonzero after changing its additive scale. -/
theorem realWhittakerModel_ne_bot_mul {r : ℕ} {ds : List RealBlock} {a b : ℝˣ}
    (hB : realWhittakerModel r ds b ≠ ⊥) : realWhittakerModel r ds (b * a) ≠ ⊥ := by
  obtain ⟨W, hW, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  let m := leadingCharacterDiagonal r r a
  have hw : leftTranslate m W ∈ realWhittakerModel r ds (b * a) :=
    leftTranslate_leading_mem_model le_rfl hW
  intro hz
  rw [hz, Submodule.mem_bot] at hw
  apply hne
  funext g
  simpa only [leftTranslate_apply, mul_inv_cancel_left, Pi.zero_apply] using congrFun hw (m⁻¹ * g)

private theorem hasLeftCharacter_model {r : ℕ} {ds : List RealBlock} {a : ℝˣ} {W : G r → ℂ}
    (hW : W ∈ realWhittakerModel r ds a) : HasLeftCharacter a W :=
  (RealLocalWhittaker.model_le_regularFunctions ds a hW).1

/-- The measure data after left multiplication on the quotient by the leading
character diagonal, using the transported Haar measures. -/
def leadingCharacterMeasure {r : ℕ} (q : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData r) :
    RealQuotientMeasureData r :=
  changeQuotientMeasure (leadingCharacterDiagonal r q a)
    (conjugation_diagonal_mem_iff (fun i : Fin (r + 1) => a ^ (q - i.val))) D

private def leadingCharacterShift {r : ℕ} (q : ℕ) (a : ℝˣ) :
    LeftUnipotentQuotient r ℝ ≃ₜ LeftUnipotentQuotient r ℝ :=
  shiftQuotient (leadingCharacterDiagonal r q a)
    (conjugation_diagonal_mem_iff (fun i : Fin (r + 1) => a ^ (q - i.val))) 1

private theorem leadingCharacterShift_mk {r : ℕ} (q : ℕ) (a : ℝˣ) (g : G r) :
    leadingCharacterShift q a (Quotient.mk _ g) =
      Quotient.mk _ (leadingCharacterDiagonal r q a * g) := by
  rw [leadingCharacterShift, shiftQuotient_mk, mul_one]

private theorem measurePreserving_leadingCharacterShift {r : ℕ} (q : ℕ) (a : ℝˣ)
    (D : RealQuotientMeasureData r) :
    MeasurePreserving (leadingCharacterShift q a) D.measure (leadingCharacterMeasure q a D).measure :=
  measurePreserving_shiftQuotient _ _ D 1

private theorem lastRow_leadingCharacterDiagonal_mul {r : ℕ} (a : ℝˣ) (g : G r) :
    Langlands.RankinSelberg.lastRow (leadingCharacterDiagonal r r a * g) =
      Langlands.RankinSelberg.lastRow g := by
  funext j
  change ((leadingCharacterDiagonal r r a * g).val) (Fin.last r) j = g.val (Fin.last r) j
  simp only [leadingCharacterDiagonal, Units.val_mul, diagonalUnits_val, Matrix.diagonal_mul,
    Fin.val_last, Nat.sub_self, pow_zero, Units.val_one, one_mul]

private theorem leadingCharacter_abs_det_eq_one {r : ℕ} (q : ℕ) {a : ℝˣ} (ha : |(a : ℝ)| = 1) :
    |(leadingCharacterDiagonal r q a).val.det| = 1 := by
  rw [leadingCharacterDiagonal, diagonalUnits_val, Matrix.det_diagonal, Finset.abs_prod]
  simp [Units.val_pow_eq_pow_val, abs_pow, ha]

private theorem detPower_neg_mul (r : ℕ) (m g : G r) (s : ℂ) :
    P m (-s) * P (m * g) s = P g s := by
  rw [realDetPower_mul, ← mul_assoc]
  have hm : P m (-s) * P m s = 1 := by
    simp only [ArchimedeanLocal.detPower, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  rw [hm, one_mul]

private theorem equalIntegrand_mk {r : ℕ} {a : ℝˣ} {W V : G r → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ) (g : G r) :
    realEqualIntegrand W V Φ s (Quotient.mk _ g) =
      W g * V g * Φ (Langlands.RankinSelberg.lastRow g) * P g s := by
  let f : G r → ℂ := fun y => W y * V y * Φ (Langlands.RankinSelberg.lastRow y) * P y s
  have hf (u : GeneralLinear.upperUnipotent (r + 1) ℝ) (y : G r) : f (u.val * y) = f y := by
    dsimp [f]
    have hp : P (u.val * y) s = P y s := by
      simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul,
        Langlands.RankinSelberg.unipotent_det, one_mul]
    rw [hW _ u.2, hV _ u.2, Langlands.RankinSelberg.lastRow_unipotent_mul, hp]
    congr 2
    calc
      _ = (realWhittakerCharacter a u.val * realWhittakerCharacter (-a) u.val) * (W y * V y) := by ring
      _ = _ := by rw [realWhittakerCharacter_mul_neg, one_mul]
  exact congrArg (Langlands.QuotientIntegration.descend _ f hf) (Quotient.out_eq (Quotient.mk _ g))

private def transportNormalization {I J L c : ℂ → ℂ}
    (N : OrdinaryIntegralNormalization J L) (hc : Differentiable ℂ c)
    (h : ∀ s, I s = c s * J s) : OrdinaryIntegralNormalization I L where
  value s := c s * N.value s
  analytic := (hc.differentiableOn.analyticOnNhd isOpen_univ).mul N.analytic
  eq_on_right := by
    obtain ⟨b, hb⟩ := N.eq_on_right
    exact ⟨b, fun s hs => by rw [h s, hb s hs, mul_assoc]⟩

private theorem covering_transport {T T' : Type*} {J : T → ℂ → ℂ} {I : T' → ℂ → ℂ}
    {L : ReciprocalEntire} (j : T → T') {c : ℂ → ℂ} (hc : Differentiable ℂ c)
    (hne : ∀ s, c s ≠ 0) (h : ∀ i s, I (j i) s = c s * J i s)
    (hcov : HasCoveringOrdinaryNormalizations J L) : HasCoveringOrdinaryNormalizations I L := by
  intro s
  obtain ⟨i, N, hN⟩ := hcov s
  exact ⟨j i, transportNormalization N hc (h i), mul_ne_zero (hne s) hN⟩

private theorem finiteSum_transport {T T' : Type*} {J : T → ℂ → ℂ} {I : T' → ℂ → ℂ}
    {L : ReciprocalEntire} (j : T → T') {c : ℂ → ℂ} (hc : Differentiable ℂ c)
    (hone : ∀ s, c s = 1) (h : ∀ i s, I (j i) s = c s * J i s)
    (hfin : HasFiniteOrdinaryNormalizationSum J L) : HasFiniteOrdinaryNormalizationSum I L := by
  obtain ⟨n, i, N, hN⟩ := hfin
  refine ⟨n, j ∘ i, fun k => transportNormalization (N k) hc (h (i k)), fun s => ?_⟩
  change ∑ k, c s * (N k).value s = 1
  simpa only [hone s, one_mul] using hN s

section Equal

variable {r : ℕ} {d e : List RealBlock}

private abbrev EqualTest (r : ℕ) (d e : List RealBlock) (a : ℝˣ) :=
  realWhittakerModel r d a × realWhittakerModel r e (-a) × SchwartzMap (Fin (r + 1) → ℝ) ℂ

private def scaleEqualTest (a : ℝˣ) (i : EqualTest r d e 1) : EqualTest r d e a :=
  (⟨leftTranslate (leadingCharacterDiagonal r r a) i.1.val, by
    simpa only [one_mul] using leftTranslate_leading_mem_model (a := a) le_rfl i.1.2⟩,
   ⟨leftTranslate (leadingCharacterDiagonal r r a) i.2.1.val, by
    simpa only [neg_mul, one_mul] using leftTranslate_leading_mem_model (a := a) le_rfl i.2.1.2⟩,
   i.2.2)

private theorem scaleEqualTest_integral (a : ℝˣ) (D : RealQuotientMeasureData r)
    (i : EqualTest r d e 1) (s : ℂ) :
    realOrdinaryEqualTest r d e a D (scaleEqualTest a i) s =
      P (leadingCharacterDiagonal r r a) (-s) *
        realOrdinaryEqualTest r d e 1 (leadingCharacterMeasure r a D) i s := by
  let m := leadingCharacterDiagonal r r a
  let W := (scaleEqualTest a i).1
  let V := (scaleEqualTest a i).2.1
  let Φ := i.2.2
  have hW (g : G r) : W.val g = i.1.val (m * g) := rfl
  have hV (g : G r) : V.val g = i.2.1.val (m * g) := rfl
  have hK : realEqualIntegrand W V Φ s = fun x => P m (-s) *
      realEqualIntegrand i.1 i.2.1 Φ s (leadingCharacterShift r a x) := by
    funext x
    induction x using Quotient.inductionOn with
    | _ g =>
      rw [leadingCharacterShift_mk, equalIntegrand_mk (hasLeftCharacter_model W.2)
        (hasLeftCharacter_model V.2), equalIntegrand_mk (hasLeftCharacter_model i.1.2)
        (hasLeftCharacter_model i.2.1.2), hW, hV, lastRow_leadingCharacterDiagonal_mul]
      rw [← detPower_neg_mul r m g s]
      ring
  change (∫ x, realEqualIntegrand W V Φ s x ∂D.measure) = _
  rw [hK, integral_const_mul, (measurePreserving_leadingCharacterShift r a D).integral_comp
    (leadingCharacterShift r a).measurableEmbedding]
  rfl

private theorem differentiable_equalMultiplier (a : ℝˣ) :
    Differentiable ℂ (fun s => P (leadingCharacterDiagonal r r a) (-s)) := by
  unfold ArchimedeanLocal.detPower
  exact (differentiable_neg.mul_const _).cexp

/-- Pointwise coverage for the ordinary real equal-rank tests at scale `1`
implies pointwise coverage at any additive scale. -/
theorem realEqualCoverage_scale (a : ℝˣ) (D : RealQuotientMeasureData r)
    (h : HasCoveringOrdinaryNormalizations
      (realOrdinaryEqualTest r d e 1 (leadingCharacterMeasure r a D)) (realPairLFactor d e)) :
    HasCoveringOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e) :=
  covering_transport (scaleEqualTest a) (differentiable_equalMultiplier a)
    (fun _ => Complex.exp_ne_zero _) (scaleEqualTest_integral a D) h

/-- A finite sum of normalized ordinary real equal-rank tests at scale `1`
transfers to any additive scale of absolute value one. -/
theorem realEqualFiniteSum_scale (a : ℝˣ) (ha : |(a : ℝ)| = 1) (D : RealQuotientMeasureData r)
    (h : HasFiniteOrdinaryNormalizationSum
      (realOrdinaryEqualTest r d e 1 (leadingCharacterMeasure r a D)) (realPairLFactor d e)) :
    HasFiniteOrdinaryNormalizationSum (realOrdinaryEqualTest r d e a D) (realPairLFactor d e) :=
  finiteSum_transport (scaleEqualTest a) (differentiable_equalMultiplier a)
    (fun _ => by simp [ArchimedeanLocal.detPower, realNormalizedAbs, leadingCharacter_abs_det_eq_one r ha])
    (scaleEqualTest_integral a D) h

end Equal

section Unequal

variable {r t : ℕ} {d e : List RealBlock}

private abbrev pad (h : t < r) : G t →* G r :=
  padGL (Nat.le_of_lt (Nat.succ_lt_succ h))

/-- The right correction for an ordinary unequal-rank test. It is the identity on
the leading block and the inverse of the character diagonal on the trailing block. -/
def unequalScaleCorrection (r t : ℕ) (a : ℝˣ) : G r :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) fun i : Fin (r + 1) =>
    if i.val < t + 1 then 1 else (a ^ (r - i.val))⁻¹

private theorem leadingCharacterDiagonal_pad (h : t < r) (a : ℝˣ) (g : G t) :
    leadingCharacterDiagonal r r a * pad h g * unequalScaleCorrection r t a =
      pad h (leadingCharacterDiagonal t r a * g) := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, leadingCharacterDiagonal, unequalScaleCorrection, diagonalUnits_val,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [UnequalAnalytic.padGL_apply, UnequalAnalytic.padGL_apply]
  by_cases hij : i.val < t + 1 ∧ j.val < t + 1
  · simp [hij, Units.val_mul, diagonalUnits_val, Matrix.diagonal_mul]
  · by_cases heq : i = j
    · subst j
      have hi : ¬ i.val < t + 1 := fun hi => hij ⟨hi, hi⟩
      simp [hi, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, pow_ne_zero _ a.ne_zero]
    · simp only [dite_eq_right hij, Matrix.one_apply_ne heq, mul_zero, zero_mul]

private theorem unequalScaleCorrection_eq_one (h : t + 1 = r) (a : ℝˣ) :
    unequalScaleCorrection r t a = 1 := by
  have hd (i : Fin (r + 1)) :
      (if i.val < t + 1 then 1 else (a ^ (r - i.val))⁻¹) = 1 := by
    by_cases hi : i.val < t + 1
    · simp [hi]
    · have hlast : i.val = r := by have := i.isLt; omega
      simp [hlast]
  unfold unequalScaleCorrection
  simp only [hd]
  exact map_one (Langlands.GeneralLinear.Iwasawa.diagonalUnits (F := ℝ))

private theorem unequalScaleCorrection_mem_compact {a : ℝˣ} (h : t + 1 = r ∨ |(a : ℝ)| = 1) :
    unequalScaleCorrection r t a ∈ unitaryCompact ℝ (r + 1) := by
  rcases h with h | h
  · rw [unequalScaleCorrection_eq_one h]
    exact one_mem _
  · let c (i : Fin (r + 1)) : ℝˣ := if i.val < t + 1 then 1 else (a ^ (r - i.val))⁻¹
    change (Langlands.GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) c).val ∈ Matrix.unitaryGroup _ _
    rw [diagonalUnits_val]
    change Matrix.diagonal (fun i => (c i : ℝ)) ∈ unitary _
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    have hi : |(c i : ℝ)| = 1 := by
      dsimp only [c]
      split_ifs <;> simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, abs_inv, abs_pow, h]
    have hsq : (c i : ℝ) ^ 2 = 1 := by rw [← sq_abs, hi, one_pow]
    exact Unitary.mem_iff.mpr ⟨by simpa [star_trivial, pow_two] using hsq,
      by simpa [star_trivial, pow_two] using hsq⟩

private theorem rightTranslate_mem_model {k : G r} {b : ℝˣ} {W : G r → ℂ}
    (hk : k ∈ unitaryCompact ℝ (r + 1)) (hW : W ∈ realWhittakerModel r d b) :
    ArchimedeanLocal.translateFunction k W ∈ realWhittakerModel r d b := by
  let L := Whittaker.rightTranslation ℂ (G r) k
  have hle : realWhittakerModel r d b ≤ (realWhittakerModel r d b).comap L := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    let f' : Automorphic.realStandardKFinite (r + 1) d :=
      ⟨L f, rightTranslation_mem_kFiniteFunctions_realStandardModule _ _ f.2 hk⟩
    change L (B f) ∈ realWhittakerModel r d b
    rw [← hB.2.2.2.1 ⟨k, hk⟩ f f' rfl]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f', rfl⟩)
  exact hle hW

/-- The larger ordinary coefficient after changing character and correcting the
ordinary padded argument. -/
def scaleUnequalLarge (t : ℕ) (a : ℝˣ) (W : G r → ℂ) : G r → ℂ :=
  ArchimedeanLocal.translateFunction (unequalScaleCorrection r t a)
    (leftTranslate (leadingCharacterDiagonal r r a) W)

/-- The nonvanishing entire determinant multiplier in the unequal-rank comparison. -/
def unequalScaleMultiplier (r t : ℕ) (a : ℝˣ) (s : ℂ) : ℂ :=
  P (leadingCharacterDiagonal t r a) (-(s - ((r - t : ℕ) : ℂ) / 2))

private theorem differentiable_unequalScaleMultiplier (a : ℝˣ) :
    Differentiable ℂ (unequalScaleMultiplier r t a) := by
  unfold unequalScaleMultiplier ArchimedeanLocal.detPower
  exact (((differentiable_id.sub_const _).neg).mul_const _).cexp

/-- The change of variables for the real ordinary unequal-rank integral, with
its right correction on the larger Whittaker function. -/
theorem realUnequalIntegral_scale (h : t < r) (a : ℝˣ) {b : ℝˣ}
    (D : RealQuotientMeasureData t) {W : G r → ℂ} {V : G t → ℂ}
    (hW : W ∈ realWhittakerModel r d b) (hV : V ∈ realWhittakerModel t e (-b)) (s : ℂ) :
    realUnequalIntegral h D (scaleUnequalLarge t a W)
        (leftTranslate (leadingCharacterDiagonal t r a) V) s =
      unequalScaleMultiplier r t a s * realUnequalIntegral h (leadingCharacterMeasure r a D) W V s := by
  let m := leadingCharacterDiagonal t r a
  let W' := scaleUnequalLarge t a W
  let V' := leftTranslate m V
  have hW' : HasLeftCharacter (b * a) W' := by
    intro u hu g
    change leftTranslate (leadingCharacterDiagonal r r a) W
        ((u * g) * unequalScaleCorrection r t a) = _
    rw [mul_assoc]
    exact hasLeftCharacter_model (leftTranslate_leading_mem_model le_rfl hW) u hu _
  have hV' : HasLeftCharacter (-(b * a)) V' := by
    rw [← neg_mul]
    exact hasLeftCharacter_model (leftTranslate_leading_mem_model h.le hV)
  have hK : realUnequalIntegrand h W' V' s = fun x => unequalScaleMultiplier r t a s *
      realUnequalIntegrand h W V s (leadingCharacterShift r a x) := by
    funext x
    induction x using Quotient.inductionOn with
    | _ g =>
      rw [leadingCharacterShift_mk, RealUnequalFamily.integrand_mk h hW' hV',
        RealUnequalFamily.integrand_mk h (hasLeftCharacter_model hW) (hasLeftCharacter_model hV)]
      let z := s - ((r - t : ℕ) : ℂ) / 2
      change W' (pad h g) * V' g * P g z = P m (-z) * (W (pad h (m * g)) * V (m * g) * P (m * g) z)
      have hWg : W' (pad h g) = W (pad h (m * g)) := by
        change W (leadingCharacterDiagonal r r a * (pad h g * unequalScaleCorrection r t a)) = _
        rw [← mul_assoc, leadingCharacterDiagonal_pad]
      rw [hWg, ← detPower_neg_mul t m g z]
      change _ * V (m * g) * _ = _
      ring
  change (∫ x, realUnequalIntegrand h W' V' s x ∂D.measure) = _
  rw [hK, integral_const_mul, (measurePreserving_leadingCharacterShift r a D).integral_comp
    (leadingCharacterShift r a).measurableEmbedding]
  rfl

private abbrev UnequalTest (r t : ℕ) (d e : List RealBlock) (b : ℝˣ) :=
  realWhittakerModel r d b × realWhittakerModel t e (-b)

private def scaleUnequalTest (h : t < r) (a : ℝˣ)
    (ha : t + 1 = r ∨ |(a : ℝ)| = 1) {b : ℝˣ} (i : UnequalTest r t d e b) :
    UnequalTest r t d e (b * a) :=
  (⟨scaleUnequalLarge t a i.1.val, rightTranslate_mem_model
    (unequalScaleCorrection_mem_compact ha) (leftTranslate_leading_mem_model le_rfl i.1.2)⟩,
   ⟨leftTranslate (leadingCharacterDiagonal t r a) i.2.val, by
      simpa only [neg_mul] using leftTranslate_leading_mem_model h.le i.2.2⟩)

private theorem scaleUnequalTest_integral (h : t < r) (a : ℝˣ)
    (ha : t + 1 = r ∨ |(a : ℝ)| = 1) (D : RealQuotientMeasureData t)
    {b : ℝˣ} (i : UnequalTest r t d e b) (s : ℂ) :
    realOrdinaryUnequalTest h d e (b * a) D (scaleUnequalTest h a ha i) s =
      unequalScaleMultiplier r t a s *
        realOrdinaryUnequalTest h d e b (leadingCharacterMeasure r a D) i s :=
  realUnequalIntegral_scale h a D i.1.2 i.2.2 s

/-- If the ranks are adjacent or the scale has absolute value one, pointwise ordinary
generation transfers under the real additive character change. -/
theorem realUnequalCoverage_scale (h : t < r) (a : ℝˣ) (ha : t + 1 = r ∨ |(a : ℝ)| = 1)
    (D : RealQuotientMeasureData t) {b : ℝˣ}
    (hcov : HasCoveringOrdinaryNormalizations
      (realOrdinaryUnequalTest h d e b (leadingCharacterMeasure r a D)) (realPairLFactor d e)) :
    HasCoveringOrdinaryNormalizations (realOrdinaryUnequalTest h d e (b * a) D) (realPairLFactor d e) :=
  covering_transport (scaleUnequalTest h a ha) (differentiable_unequalScaleMultiplier a)
    (fun _ => Complex.exp_ne_zero _) (scaleUnequalTest_integral h a ha D) hcov

/-- A real change of additive scale of absolute value one preserves a finite sum
of normalized ordinary unequal-rank tests with value one. -/
theorem realUnequalFiniteSum_scale (h : t < r) (a : ℝˣ) (ha : |(a : ℝ)| = 1)
    (D : RealQuotientMeasureData t) {b : ℝˣ}
    (hfin : HasFiniteOrdinaryNormalizationSum
      (realOrdinaryUnequalTest h d e b (leadingCharacterMeasure r a D)) (realPairLFactor d e)) :
    HasFiniteOrdinaryNormalizationSum (realOrdinaryUnequalTest h d e (b * a) D) (realPairLFactor d e) :=
  finiteSum_transport (scaleUnequalTest h a (Or.inr ha)) (differentiable_unequalScaleMultiplier a)
    (fun _ => by simp [unequalScaleMultiplier, ArchimedeanLocal.detPower, realNormalizedAbs,
      leadingCharacter_abs_det_eq_one r ha]) (scaleUnequalTest_integral h a (Or.inr ha) D) hfin

end Unequal

end Langlands.Global.RankinSelbergGlobal.RealCharacterChange

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic
open Langlands.LocalFactor.Archimedean RealCharacterChange

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Real ordinary normalized generation follows from finite generation in positive
equal ranks and adjacent ranks at scale `1`, and pointwise generation in ranks
of gap greater than one at positive scales. -/
def RealOrdinaryGenerationReductionStatement : Prop :=
  (∀ (r : ℕ), 0 < r → ∀ (d e : List RealBlock), realRank d = r + 1 → realRank e = r + 1 →
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (r + 1) e) (realStandardLie (r + 1) e) →
    ∀ D : RealQuotientMeasureData r,
      realWhittakerModel r d 1 ≠ ⊥ → realWhittakerModel r e (-1) ≠ ⊥ →
      HasFiniteOrdinaryNormalizationSum (realOrdinaryEqualTest r d e 1 D) (realPairLFactor d e)) →
  (∀ (r t : ℕ) (h : t < r), t + 1 = r →
    ∀ (d e : List RealBlock), realRank d = r + 1 → realRank e = t + 1 →
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (t + 1) e) (realStandardLie (t + 1) e) →
    ∀ D : RealQuotientMeasureData t,
      realWhittakerModel r d 1 ≠ ⊥ → realWhittakerModel t e (-1) ≠ ⊥ →
      HasFiniteOrdinaryNormalizationSum (realOrdinaryUnequalTest h d e 1 D) (realPairLFactor d e)) →
  (∀ (r t : ℕ) (h : t < r), t + 1 < r →
    ∀ (d e : List RealBlock), realRank d = r + 1 → realRank e = t + 1 →
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (t + 1) e) (realStandardLie (t + 1) e) →
    ∀ (a : ℝˣ), 0 < (a : ℝ) → ∀ D : RealQuotientMeasureData t,
      realWhittakerModel r d a ≠ ⊥ → realWhittakerModel t e (-a) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e)) →
  RealOrdinaryNormalizedGenerationStatement

theorem realOrdinaryGenerationReduction : RealOrdinaryGenerationReductionStatement := by
  intro hEqual hAdjacent hGap
  have standard {r : ℕ} {ds : List RealBlock} {a : ℝˣ} (hw : realWhittakerModel r ds a ≠ ⊥) :
      realWhittakerModel r ds 1 ≠ ⊥ := by
    simpa only [mul_inv_cancel] using realWhittakerModel_ne_bot_mul (a := a⁻¹) hw
  have opposite {r : ℕ} {ds : List RealBlock} {a : ℝˣ} (hw : realWhittakerModel r ds (-a) ≠ ⊥) :
      realWhittakerModel r ds (-1) ≠ ⊥ := by
    simpa only [neg_mul, mul_inv_cancel] using realWhittakerModel_ne_bot_mul (a := a⁻¹) hw
  have abs_one {a : ℝˣ} (ha : a = 1 ∨ a = -1) : |(a : ℝ)| = 1 := by
    rcases ha with rfl | rfl <;> simp
  constructor
  · intro r t h d e hd he hirr hirr' a D hW hV
    let Cov (b : ℝˣ) := HasCoveringOrdinaryNormalizations
      (realOrdinaryUnequalTest h d e b D) (realPairLFactor d e)
    let Sum (b : ℝˣ) := HasFiniteOrdinaryNormalizationSum
      (realOrdinaryUnequalTest h d e b D) (realPairLFactor d e)
    by_cases hadj : t + 1 = r
    · have hsum := hAdjacent r t h hadj d e hd he hirr hirr'
        (leadingCharacterMeasure r a D) (standard hW) (opposite hV)
      refine ⟨?_, fun _ ha => ?_⟩
      · exact (congrArg Cov (one_mul a)).mp
          (realUnequalCoverage_scale h a (Or.inl hadj) D hsum.covering)
      · exact (congrArg Sum (one_mul a)).mp
          (realUnequalFiniteSum_scale h a (abs_one ha) D hsum)
    · refine ⟨?_, fun hEq _ => (hadj hEq).elim⟩
      have hlarge : t + 1 < r := lt_of_le_of_ne h hadj
      rcases lt_or_gt_of_ne a.ne_zero with hneg | hpos
      · have hW' : realWhittakerModel r d (-a) ≠ ⊥ := by
          simpa only [mul_neg_one] using realWhittakerModel_ne_bot_mul (a := -1) hW
        have hV' : realWhittakerModel t e (-(-a)) ≠ ⊥ := by
          simpa only [mul_neg_one] using realWhittakerModel_ne_bot_mul (a := -1) hV
        have hpos' : 0 < ((-a : ℝˣ) : ℝ) := by simpa only [Units.val_neg, neg_pos] using hneg
        have hcov := hGap r t h hlarge d e hd he hirr hirr' (-a) hpos'
          (leadingCharacterMeasure r (-1) D) hW' hV'
        have ha : -a * (-1 : ℝˣ) = a := by simp
        exact (congrArg Cov ha).mp (realUnequalCoverage_scale h (-1) (Or.inr (by simp)) D hcov)
      · exact hGap r t h hlarge d e hd he hirr hirr' a hpos D hW hV
  · intro r d e hd he hirr hirr' a D hW hV
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have hsum := (rankOneOrdinaryNormalizedTests.1 d e hd he a D).2 hW hV
      exact ⟨hsum.covering, fun _ => hsum⟩
    · have hsum := hEqual r hr d e hd he hirr hirr' (leadingCharacterMeasure r a D)
        (standard hW) (opposite hV)
      exact ⟨realEqualCoverage_scale a D hsum.covering, fun ha => realEqualFiniteSum_scale a (abs_one ha) D hsum⟩

end Langlands.Global.RankinSelbergGlobal
