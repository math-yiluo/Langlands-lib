import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.ComplexLocalEqualCharacterReduction
import Langlands.Global.RankinSelberg.ComplexUnequalFamilyKernels
import Langlands.Global.RankinSelberg.StandardCompactPadding
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight

/-! # Change of additive character for ordinary complex normalized tests -/

noncomputable section

open MeasureTheory Set

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit phaseUnit_val diagonalUnits_phaseUnit_mem)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val)
open ComplexUnequalFamily (HasLeftCharacter ordinaryKernel_mk)
open Langlands.GodementJacquet (detPower_complex_mul detPower_complex_add)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
private abbrev pairL (d e : List ComplexCharacterData) (s : ℂ) : ℂ :=
  ((complexPairLFactor d e).denominator s)⁻¹

private theorem changeDiagonal_inv (r : ℕ) (a : ℂˣ) :
    changeDiagonal r a⁻¹ = (changeDiagonal r a)⁻¹ := by
  simp only [changeDiagonal, ← map_inv]
  congr 1

/-- Left multiplication by the character diagonal takes standard Whittaker functions
to the indicated trace scale. -/
def scaleWhittaker {r : ℕ} (a : ℂˣ) (W : G (r + 1) → ℂ) : G (r + 1) → ℂ :=
  leftTranslate (changeDiagonal r a) W

theorem scaleWhittaker_mem {r : ℕ} {d : List ComplexCharacterData} {a : ℂˣ}
    {W : G (r + 1) → ℂ} (hW : W ∈ complexWhittakerModel r d 1) :
    scaleWhittaker a W ∈ complexWhittakerModel r d a := by
  simpa only [scaleWhittaker, changeDiagonal_inv, inv_inv, one_mul] using
    leftTranslate_mem_model a⁻¹ 1 hW

theorem scaleWhittaker_neg_mem {r : ℕ} {e : List ComplexCharacterData} {a : ℂˣ}
    {V : G (r + 1) → ℂ} (hV : V ∈ complexWhittakerModel r e (-1)) :
    scaleWhittaker a V ∈ complexWhittakerModel r e (-a) := by
  simpa only [scaleWhittaker, changeDiagonal_inv, inv_inv, neg_mul, one_mul] using
    leftTranslate_mem_model a⁻¹ (-1) hV

private theorem normalize_scaleWhittaker {r : ℕ} (a : ℂˣ) (W : G (r + 1) → ℂ) :
    normalizeWhittaker a (scaleWhittaker a W) = W := by
  funext g
  simp [scaleWhittaker, normalizeWhittaker]

private def transportNormalization {I J F c : ℂ → ℂ}
    (N : OrdinaryIntegralNormalization J F) (hc : Differentiable ℂ c)
    (h : ∀ s, I s = c s * J s) : OrdinaryIntegralNormalization I F where
  value s := c s * N.value s
  analytic := (hc.differentiableOn.analyticOnNhd isOpen_univ).mul N.analytic
  eq_on_right := by
    obtain ⟨b, hb⟩ := N.eq_on_right
    exact ⟨b, fun s hs => by rw [h s, hb s hs, mul_assoc]⟩

private def scaleEqualTest {r : ℕ} {d e : List ComplexCharacterData} (a : ℂˣ)
    (i : complexWhittakerModel r d 1 × complexWhittakerModel r e (-1) ×
      SchwartzMap (Fin (r + 1) → ℂ) ℂ) :
    complexWhittakerModel r d a × complexWhittakerModel r e (-a) ×
      SchwartzMap (Fin (r + 1) → ℂ) ℂ :=
  (⟨scaleWhittaker a i.1.val, scaleWhittaker_mem i.1.2⟩,
    ⟨scaleWhittaker a i.2.1.val, scaleWhittaker_neg_mem i.2.1.2⟩, i.2.2)

private theorem scaleEqualTest_integral {r : ℕ} {d e : List ComplexCharacterData} (a : ℂˣ)
    (D : ComplexQuotientMeasureData r) (i : complexWhittakerModel r d 1 ×
      complexWhittakerModel r e (-1) × SchwartzMap (Fin (r + 1) → ℂ) ℂ) (s : ℂ) :
    complexOrdinaryEqualTest r d e a D (scaleEqualTest a i) s =
      primalMultiplier r a s * complexOrdinaryEqualTest r d e 1 (changeQuotientMeasure a D) i s := by
  rcases i with ⟨⟨W, hW⟩, ⟨V, hV⟩, Φ⟩
  dsimp only [complexOrdinaryEqualTest, scaleEqualTest]
  have h := (primal_comparison (scaleWhittaker_mem (a := a) hW)
    (scaleWhittaker_neg_mem (a := a) hV) D Φ s).2
  rw [normalize_scaleWhittaker, normalize_scaleWhittaker] at h
  exact h

private def scaleEqualNormalization {r : ℕ} {d e : List ComplexCharacterData} {a : ℂˣ}
    {D : ComplexQuotientMeasureData r} {i : complexWhittakerModel r d 1 ×
      complexWhittakerModel r e (-1) × SchwartzMap (Fin (r + 1) → ℂ) ℂ}
    (N : OrdinaryIntegralNormalization (complexOrdinaryEqualTest r d e 1 (changeQuotientMeasure a D) i)
      (pairL d e)) :
    OrdinaryIntegralNormalization (complexOrdinaryEqualTest r d e a D (scaleEqualTest a i))
      (pairL d e) :=
  transportNormalization N (differentiable_primalMultiplier r a) (scaleEqualTest_integral a D i)

/-- Ordinary equal-rank normalized coverage transfers from the standard trace character
along the transported quotient measure. -/
theorem complexEqualCoverage_scale {r : ℕ} {d e : List ComplexCharacterData}
    (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (h : HasCoveringOrdinaryNormalizations
      (complexOrdinaryEqualTest r d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e)) :
    HasCoveringOrdinaryNormalizations (complexOrdinaryEqualTest r d e a D) (complexPairLFactor d e) := by
  intro s
  obtain ⟨i, N, hN⟩ := h s
  refine ⟨scaleEqualTest a i, scaleEqualNormalization N, ?_⟩
  change primalMultiplier r a s * N.value s ≠ 0
  exact mul_ne_zero (amplitude_ne_zero _ _) hN

/-- A finite sum of ordinary equal-rank normalized values is preserved by a unit-norm
change of trace parameter, in particular by the change from `1` to `-1`. -/
theorem complexEqualFiniteSum_scale {r : ℕ} {d e : List ComplexCharacterData}
    (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) (D : ComplexQuotientMeasureData r)
    (h : HasFiniteOrdinaryNormalizationSum
      (complexOrdinaryEqualTest r d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e)) :
    HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest r d e a D) (complexPairLFactor d e) := by
  obtain ⟨n, i, N, hN⟩ := h
  refine ⟨n, fun j => scaleEqualTest a (i j), fun j => scaleEqualNormalization (N j), fun s => ?_⟩
  change ∑ j, primalMultiplier r a s * (N j).value s = 1
  simpa [primalMultiplier, amplitude, ha] using hN s

variable {r t : ℕ}

abbrev unequalPadHom (h : t < r) : G (t + 1) →* G (r + 1) :=
  padGL (Nat.succ_le_succ h.le)

local notation "pad" => unequalPadHom

/-- The diagonal right factor which makes the two changes of Whittaker character
agree on the ordinary padded argument. -/
def unequalScaleCorrection (h : t < r) (a : ℂˣ) : G (r + 1) :=
  (changeDiagonal r a)⁻¹ * pad h (changeDiagonal t a)

private theorem pad_conj (h : t < r) (a : ℂˣ) (g : G (t + 1)) :
    changeDiagonal r a * pad h g * (changeDiagonal r a)⁻¹ =
      pad h (changeDiagonal t a * g * (changeDiagonal t a)⁻¹) := by
  apply Units.ext
  ext i j
  simp only [changeDiagonal, ← map_inv, Units.val_mul, diagonalUnits_val, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Pi.inv_apply]
  rw [UnequalAnalytic.padGL_apply, UnequalAnalytic.padGL_apply]
  split
  · rename_i hij
    have hi : r - i.val = t - i.val + (r - t) := by omega
    have hj : r - j.val = t - j.val + (r - t) := by omega
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    rw [hi, hj, pow_add, pow_add, mul_inv_rev]
    calc
      _ = (↑a ^ (r - t) * (↑a ^ (r - t))⁻¹) *
          (↑a ^ (t - i.val) * g.val ⟨i, hij.1⟩ ⟨j, hij.2⟩ * (↑a ^ (t - j.val))⁻¹) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ (pow_ne_zero _ a.ne_zero), one_mul]
        simp only [Units.val_mul, diagonalUnits_val, Matrix.diagonal_mul, Matrix.mul_diagonal,
          Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  ·
    by_cases heq : i = j
    · subst j
      simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, a.ne_zero]
    · simp [Matrix.one_apply_ne heq]

/-- The padded evaluation after the two translations is precisely the padding of the
translated smaller-rank argument. -/
theorem shift_pad_unequalScaleCorrection (h : t < r) (a : ℂˣ) (g : G (t + 1)) :
    changeDiagonal r a * pad h g * unequalScaleCorrection h a = pad h (changeDiagonal t a * g) := by
  rw [unequalScaleCorrection, ← mul_assoc, pad_conj, ← map_mul, inv_mul_cancel_right]

/-- The determinant contribution under the quotient substitution in unequal rank. -/
def unequalScaleMultiplier (_h : t < r) (a : ℂˣ) (s : ℂ) : ℂ :=
  P (changeDiagonal t a) (-(s - ((r - t : ℕ) : ℂ) / 2))

theorem differentiable_unequalScaleMultiplier (h : t < r) (a : ℂˣ) :
    Differentiable ℂ (unequalScaleMultiplier h a) := by
  unfold unequalScaleMultiplier ArchimedeanLocal.detPower
  exact (((differentiable_id.sub_const _).neg).mul_const _).cexp

theorem unequalScaleMultiplier_ne_zero (h : t < r) (a : ℂˣ) (s : ℂ) :
    unequalScaleMultiplier h a s ≠ 0 := Complex.exp_ne_zero _

/-- The exact change of ordinary unequal-rank integral for a standard-character pair.
The larger function uses the right correction as well as the left character change. -/
theorem unequal_primal_comparison (h : t < r) {d e : List ComplexCharacterData}
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) {W : G (r + 1) → ℂ} {V : G (t + 1) → ℂ}
    (hW : W ∈ complexWhittakerModel r d 1) (hV : V ∈ complexWhittakerModel t e (-1)) (s : ℂ) :
    complexUnequalIntegral h D (ArchimedeanLocal.translateFunction (unequalScaleCorrection h a) (scaleWhittaker a W))
      (scaleWhittaker a V) s = unequalScaleMultiplier h a s *
      complexUnequalIntegral h (changeQuotientMeasure a D) W V s := by
  let Wₐ := scaleWhittaker a W
  let Vₐ := scaleWhittaker a V
  let Wₐ' := ArchimedeanLocal.translateFunction (unequalScaleCorrection h a) Wₐ
  have hLeft {l : ℕ} {c : ℂˣ} {ds : List ComplexCharacterData} {U : G (l + 1) → ℂ}
      (hU : U ∈ complexWhittakerModel l ds c) : HasLeftCharacter c U :=
    fun u g => complexWhittakerModel_left_equivariant hU u.val u.2 g
  have hWₐ : HasLeftCharacter a Wₐ' := by
    intro u g
    change Wₐ ((u.val * g) * _) = _
    rw [mul_assoc]
    exact hLeft (scaleWhittaker_mem hW) u _
  have hVₐ : HasLeftCharacter (-a) Vₐ := hLeft (scaleWhittaker_neg_mem hV)
  have hK : complexUnequalIntegrand h Wₐ' Vₐ s = fun q => unequalScaleMultiplier h a s *
      complexUnequalIntegrand h W V s (shiftQuotient a 1 q) := by
    funext q
    induction q using Quotient.inductionOn with
    | _ g =>
      rw [shiftQuotient_mk, mul_one, ordinaryKernel_mk h hWₐ hVₐ, ordinaryKernel_mk h (hLeft hW) (hLeft hV)]
      let z := s - ((r - t : ℕ) : ℂ) / 2
      have hd : unequalScaleMultiplier h a s * P (changeDiagonal t a) z = 1 := by
        change P (changeDiagonal t a) (-z) * P (changeDiagonal t a) z = 1
        rw [← detPower_complex_add, neg_add_cancel]
        simp [ArchimedeanLocal.detPower]
      simp only [Wₐ', Wₐ, Vₐ, ArchimedeanLocal.translateFunction, scaleWhittaker,
        leftTranslate_apply, ← mul_assoc]
      rw [shift_pad_unequalScaleCorrection, detPower_complex_mul]
      calc
        _ = (unequalScaleMultiplier h a s * P (changeDiagonal t a) z) * _ := by rw [hd, one_mul]
        _ = _ := by ring
  change (∫ q, complexUnequalIntegrand h Wₐ' Vₐ s q ∂D.measure) = _
  rw [hK, integral_const_mul, (measurePreserving_shiftQuotient a D 1).integral_comp
    (shiftQuotient a 1).measurableEmbedding]
  rfl

private theorem changeDiagonal_mem_unitary (l : ℕ) {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) :
    changeDiagonal l a ∈ unitaryCompact ℂ (l + 1) := by
  let d (j : Fin (l + 1)) := a ^ (l - j.val)
  have hd (j : Fin (l + 1)) : phaseUnit (d j) = d j := by
    apply Units.ext
    rw [phaseUnit_val, show ‖(d j : ℂ)‖ = 1 by simp [d, norm_pow, ha], Complex.ofReal_one, div_one]
  change GeneralLinear.Iwasawa.diagonalUnits d ∈ unitaryCompact ℂ (l + 1)
  simpa only [hd] using diagonalUnits_phaseUnit_mem d

/-- At a unit-norm scale the right factor preserves the finite Whittaker model. -/
theorem unequalScaleCorrection_mem_unitary (h : t < r) {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) :
    unequalScaleCorrection h a ∈ unitaryCompact ℂ (r + 1) := by
  exact mul_mem (inv_mem (changeDiagonal_mem_unitary r ha))
    (unitary_padGL (Nat.succ_le_succ h.le) _ (changeDiagonal_mem_unitary t ha))

/-- At a unit-norm scale the determinant multiplier in the ordinary comparison is one. -/
theorem unequalScaleMultiplier_one (h : t < r) {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) (s : ℂ) :
    unequalScaleMultiplier h a s = 1 := by
  have hnorm : ‖(changeDiagonal t a).val.det‖ = 1 := by
    rw [changeDiagonal, diagonalUnits_val, Matrix.det_diagonal, norm_prod]
    simp [norm_pow, ha]
  simp [unequalScaleMultiplier, ArchimedeanLocal.detPower, complexNormalizedAbs, hnorm]

private def scaleUnequalTest (h : t < r) {d e : List ComplexCharacterData} (a : ℂˣ)
    (ha : ‖(a : ℂ)‖ = 1) (i : complexWhittakerModel r d 1 × complexWhittakerModel t e (-1)) :
    complexWhittakerModel r d a × complexWhittakerModel t e (-a) :=
  (⟨ArchimedeanLocal.translateFunction (unequalScaleCorrection h a) (scaleWhittaker a i.1.val),
    rightTranslation_mem_complexWhittakerModel (scaleWhittaker_mem i.1.2)
      ⟨unequalScaleCorrection h a, unequalScaleCorrection_mem_unitary h ha⟩⟩,
    ⟨scaleWhittaker a i.2.val, scaleWhittaker_neg_mem i.2.2⟩)

private theorem scaleUnequalTest_integral (h : t < r) {d e : List ComplexCharacterData} (a : ℂˣ)
    (ha : ‖(a : ℂ)‖ = 1) (D : ComplexQuotientMeasureData t)
    (i : complexWhittakerModel r d 1 × complexWhittakerModel t e (-1)) (s : ℂ) :
    complexOrdinaryUnequalTest h d e a D (scaleUnequalTest h a ha i) s =
      complexOrdinaryUnequalTest h d e 1 (changeQuotientMeasure a D) i s := by
  rcases i with ⟨⟨W, hW⟩, ⟨V, hV⟩⟩
  dsimp only [complexOrdinaryUnequalTest, scaleUnequalTest]
  rw [unequal_primal_comparison h a D hW hV, unequalScaleMultiplier_one h ha s, one_mul]

private def scaleUnequalNormalization (h : t < r) {d e : List ComplexCharacterData} {a : ℂˣ}
    (ha : ‖(a : ℂ)‖ = 1) {D : ComplexQuotientMeasureData t}
    {i : complexWhittakerModel r d 1 × complexWhittakerModel t e (-1)}
    (N : OrdinaryIntegralNormalization (complexOrdinaryUnequalTest h d e 1 (changeQuotientMeasure a D) i)
      (pairL d e)) :
    OrdinaryIntegralNormalization (complexOrdinaryUnequalTest h d e a D (scaleUnequalTest h a ha i))
      (pairL d e) where
  value := N.value
  analytic := N.analytic
  eq_on_right := by
    obtain ⟨b, hb⟩ := N.eq_on_right
    exact ⟨b, fun s hs => (scaleUnequalTest_integral h a ha D i s).trans (hb s hs)⟩

/-- Pointwise unequal-rank coverage transfers to every unit-norm trace parameter. -/
theorem complexUnequalCoverage_scale (h : t < r) {d e : List ComplexCharacterData}
    (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) (D : ComplexQuotientMeasureData t)
    (hGen : HasCoveringOrdinaryNormalizations
      (complexOrdinaryUnequalTest h d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e)) :
    HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest h d e a D) (complexPairLFactor d e) := by
  intro s
  obtain ⟨i, N, hN⟩ := hGen s
  exact ⟨scaleUnequalTest h a ha i, scaleUnequalNormalization h ha N, hN⟩

/-- A finite sum of ordinary unequal-rank normalized values equal to one transfers
to every unit-norm trace parameter. -/
theorem complexUnequalFiniteSum_scale (h : t < r) {d e : List ComplexCharacterData}
    (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) (D : ComplexQuotientMeasureData t)
    (hGen : HasFiniteOrdinaryNormalizationSum
      (complexOrdinaryUnequalTest h d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e)) :
    HasFiniteOrdinaryNormalizationSum (complexOrdinaryUnequalTest h d e a D) (complexPairLFactor d e) := by
  obtain ⟨n, i, N, hN⟩ := hGen
  exact ⟨n, fun j => scaleUnequalTest h a ha (i j), fun j => scaleUnequalNormalization h ha (N j), hN⟩

/-- A standard-character covering or finite-sum family transports to the prescribed
trace character and quotient measure. Coverage is preserved for all scales in equal rank
and for unit-norm scales in unequal rank. Finite sums are preserved at unit-norm scales. -/
def ComplexOrdinaryCharacterTransportStatement : Prop :=
  (∀ (r : ℕ) (d e : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData r),
    (HasCoveringOrdinaryNormalizations
        (complexOrdinaryEqualTest r d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e) →
      HasCoveringOrdinaryNormalizations (complexOrdinaryEqualTest r d e a D) (complexPairLFactor d e)) ∧
    (‖(a : ℂ)‖ = 1 → HasFiniteOrdinaryNormalizationSum
        (complexOrdinaryEqualTest r d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e) →
      HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest r d e a D) (complexPairLFactor d e))) ∧
  ∀ (r t : ℕ) (h : t < r) (d e : List ComplexCharacterData) (a : ℂˣ)
    (D : ComplexQuotientMeasureData t), ‖(a : ℂ)‖ = 1 →
    (HasCoveringOrdinaryNormalizations
        (complexOrdinaryUnequalTest h d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e) →
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest h d e a D) (complexPairLFactor d e)) ∧
    (HasFiniteOrdinaryNormalizationSum
        (complexOrdinaryUnequalTest h d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e) →
      HasFiniteOrdinaryNormalizationSum (complexOrdinaryUnequalTest h d e a D) (complexPairLFactor d e))

theorem complexOrdinaryCharacterTransport : ComplexOrdinaryCharacterTransportStatement :=
  ⟨fun _ _ _ a D => ⟨complexEqualCoverage_scale a D, fun ha => complexEqualFiniteSum_scale a ha D⟩,
    fun _ _ h _ _ a D ha => ⟨complexUnequalCoverage_scale h a ha D, complexUnequalFiniteSum_scale h a ha D⟩⟩

end Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange
