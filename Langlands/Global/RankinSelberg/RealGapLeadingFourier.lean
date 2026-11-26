import Langlands.Global.RankinSelberg.RealGapColumnFourier
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-! # Real Fourier exchange between a leading matrix slice and the complementary rows -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapLeadingFourier

open ArchimedeanLocal (realNormalizedAbs realSelfDualMeasure)
open Langlands.LocalFactor.Archimedean (realScaledCharacter)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar)
open RealGapColumnFourier (psi psi_neg)
open RealGodement (realRectangularSchwartzFourier realRectangularSchwartzFourier_apply
  joinRectangularCoordinates realGodementRectangularFourier)

local notation "Mat" => fun n l => Matrix (Fin n) (Fin l) ℝ
local notation "G" => fun n => Langlands.GeneralLinear n ℝ

/-- The rectangular Fourier integral with the positive real character `ψ_a`. -/
def rectFourier (a : ℝˣ) {k l : ℕ} (Φ : Mat k l → ℂ) (Y : Mat k l) : ℂ :=
  ∫ X, Φ X * psi a (∑ i, ∑ j, X i j * Y i j) ∂rectangularMeasure (realSelfDualMeasure a) k l

/-- The positive real trace transform on rectangular Schwartz functions. -/
def rectTransform {n l : ℕ} (a : ℝˣ) (Φ : 𝓢(Mat n l, ℂ)) : 𝓢(Mat n l, ℂ) :=
  realRectangularSchwartzFourier a Φ

@[simp] theorem rectTransform_apply {n l : ℕ} (a : ℝˣ) (Φ : 𝓢(Mat n l, ℂ)) (Y : Mat n l) :
    rectTransform a Φ Y = rectFourier a Φ Y := by
  rw [rectTransform, realRectangularSchwartzFourier_apply]
  rfl

private theorem schwartzFourier_eq {n l : ℕ} (a : ℝˣ) (Φ : 𝓢(Mat n l, ℂ)) (Y : Mat n l) :
    realRectangularSchwartzFourier a Φ Y = rectFourier a Φ Y :=
  rectTransform_apply a Φ Y

private theorem realVolume_map_mul (a : ℝ) (ha : a ≠ 0) :
    (volume : Measure ℝ).map (fun x : ℝ => a * x) = (nnnormHom a)⁻¹ • (volume : Measure ℝ) := by
  change (volume : Measure ℝ).map (fun x : ℝ => a • x) = _
  rw [Measure.map_addHaar_smul volume ha, Module.finrank_self, pow_one, abs_inv]
  rw [← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

private def leftMul (l : ℕ) {n : ℕ} (g : G n) : Mat n l ≃L[ℝ] Mat n l :=
  { toFun := fun X => g.val * X
    invFun := fun X => g⁻¹.val * X
    left_inv X := by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    right_inv X := by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    map_add' X Y := Matrix.mul_add _ _ _
    map_smul' c X := Matrix.mul_smul _ _ _
    continuous_toFun := continuous_const.matrix_mul continuous_id
    continuous_invFun := continuous_const.matrix_mul continuous_id }

/-- Left multiplication pulls rectangular Schwartz functions back to Schwartz functions. -/
def pullRectangle {n l : ℕ} (g : G n) (Φ : 𝓢(Mat n l, ℂ)) : 𝓢(Mat n l, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (leftMul l g) Φ

@[simp] theorem pullRectangle_apply {n l : ℕ} (g : G n) (Φ : 𝓢(Mat n l, ℂ)) (X : Mat n l) :
    pullRectangle g Φ X = Φ (g.val * X) := rfl

private theorem integral_leftMul {n l : ℕ} (a : ℝˣ) (g : G n) (F : Mat n l → ℂ) :
    (∫ X, F (g.val * X) ∂rectangularMeasure (realSelfDualMeasure a) n l) =
      ((realNormalizedAbs g.val.det)⁻¹ ^ l) • ∫ X, F X ∂rectangularMeasure (realSelfDualMeasure a) n l := by
  let μ := rectangularMeasure (realSelfDualMeasure a) n l
  let : μ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let e := (leftMul l g).toHomeomorph.toMeasurableEquiv
  have h := Langlands.HarmonicAnalysis.haarMeasure_map_rectangular (volume : Measure ℝ)
    (nnnormHom : ℝ →*₀ ℝ≥0) realVolume_map_mul μ g.val (1 : Mat l l) g.det_ne_zero (by simp)
  have hm : μ.map e = (‖g.val.det‖₊ ^ l)⁻¹ • μ := by
    simpa only [show (⇑e) = (fun X => g.val * X) from rfl, Matrix.mul_one, Matrix.det_one,
      map_one, one_pow, Fintype.card_fin, mul_one, nnnormHom_apply] using h
  change (∫ X, F (e X) ∂μ) = _
  rw [← integral_map_equiv, hm, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv,
    NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, inv_pow]
  rfl

/-- Left multiplication moves to the inverse transpose in the Fourier variable. -/
theorem rectFourier_pullRectangle {n l : ℕ} (a : ℝˣ) (g : G n) (Φ : 𝓢(Mat n l, ℂ)) (Y : Mat n l) :
    rectFourier a (pullRectangle g Φ) Y = ((realNormalizedAbs g.val.det)⁻¹ ^ l) •
      rectFourier a Φ (g⁻¹.val.transpose * Y) := by
  let Z := g⁻¹.val.transpose * Y
  let K (X : Mat n l) := Φ X * psi a (∑ i, ∑ j, X i j * Z i j)
  have hPair (X : Mat n l) : (∑ i, ∑ j, (g.val * X) i j * Z i j) = ∑ i, ∑ j, X i j * Y i j := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    change dotProduct (g.val.mulVec (fun i => X i j)) (g⁻¹.val.transpose.mulVec (fun i => Y i j)) = _
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      dotProduct_comm]
    rfl
  calc
    _ = ∫ X, K (g.val * X) ∂rectangularMeasure (realSelfDualMeasure a) n l := by
      simp only [rectFourier, pullRectangle_apply, K, hPair]
    _ = _ := integral_leftMul a g K

variable (k m l : ℕ)

/-- Stack the leading matrix and the complementary rows in their consecutive positions. -/
def stackRows (X : Mat k l) (Y : Mat m l) : Mat (k + m) l := Fin.addCases X Y

@[simp] theorem stackRows_left (X : Mat k l) (Y : Mat m l) (i : Fin k) :
    stackRows k m l X Y (i.castAdd m) = X i := by simp [stackRows]

@[simp] theorem stackRows_right (X : Mat k l) (Y : Mat m l) (i : Fin m) :
    stackRows k m l X Y (i.natAdd k) = Y i := by simp [stackRows]

local notation "Idx" => Fin (k + m) × Fin l
private def inLeading (p : Idx) : Prop := p.1.val < k
local instance : DecidablePred (inLeading k m l) := fun p => Nat.decLt p.1.val k
private def outLeading (p : Idx) : Prop := ¬ inLeading k m l p
local instance : DecidablePred (outLeading k m l) := fun _ => instDecidableNot

local notation "U" => {i : Idx // inLeading k m l i}
local notation "L" => {i : Idx // ¬ inLeading k m l i}

private def leftIndices : (Fin k × Fin l) ≃ U where
  toFun p := ⟨(p.1.castAdd m, p.2), p.1.isLt⟩
  invFun p := (⟨p.val.1.val, p.2⟩, p.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def rightIndices : (Fin m × Fin l) ≃ L where
  toFun p := ⟨(p.1.natAdd k, p.2), by unfold inLeading; simp⟩
  invFun p := (⟨p.val.1.val - k, by
    have h := p.val.1.isLt
    have hp := p.2
    change ¬ p.val.1.val < k at hp
    omega⟩, p.val.2)
  left_inv p := by
    apply Prod.ext <;> try rfl
    apply Fin.ext
    change k + p.1.val - k = p.1.val
    omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> try rfl
    apply Fin.ext
    have h := p.2
    change ¬ p.val.1.val < k at h
    change k + (p.val.1.val - k) = p.val.1.val
    omega

private def toLeading : Mat k l ≃ᵐ (U → ℝ) :=
  (MeasurableEquiv.curry (Fin k) (Fin l) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (leftIndices k m l))

private def toComplement : Mat m l ≃ᵐ (L → ℝ) :=
  (MeasurableEquiv.curry (Fin m) (Fin l) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (rightIndices k m l))

private theorem constPiCongrLeft_apply {A B : Type} (e : A ≃ B) (x : A → ℝ) (i : A) :
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) e x (e i) = x i :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) e x i

private theorem toLeading_apply (X : Mat k l) (i : Fin k) (j : Fin l) :
    toLeading k m l X ⟨(i.castAdd m, j), i.isLt⟩ = X i j := by
  change MeasurableEquiv.piCongrLeft (fun _ => ℝ) (leftIndices k m l)
    ((MeasurableEquiv.curry (Fin k) (Fin l) ℝ).symm X) (leftIndices k m l (i, j)) = X i j
  rw [constPiCongrLeft_apply]
  rfl

private theorem toComplement_apply (Y : Mat m l) (i : Fin m) (j : Fin l) :
    toComplement k m l Y (rightIndices k m l (i, j)) = Y i j := by
  change MeasurableEquiv.piCongrLeft (fun _ => ℝ) (rightIndices k m l)
    ((MeasurableEquiv.curry (Fin m) (Fin l) ℝ).symm Y) (rightIndices k m l (i, j)) = Y i j
  rw [constPiCongrLeft_apply]
  rfl

private theorem measurePreserving_toLeading (a : ℝˣ) : MeasurePreserving (toLeading k m l)
    (rectangularMeasure (realSelfDualMeasure a) k l)
    (Measure.pi fun _ : U => (realSelfDualMeasure a).measure) := by
  let μ := (realSelfDualMeasure a).measure
  exact (measurePreserving_piCongrLeft (fun _ => μ) (leftIndices k m l)).comp
    (RectangleTate.measurePreserving_uncurry (fun (_ : Fin k) (_ : Fin l) => μ))

private theorem measurePreserving_toComplement (a : ℝˣ) : MeasurePreserving (toComplement k m l)
    (rectangularMeasure (realSelfDualMeasure a) m l)
    (Measure.pi fun _ : L => (realSelfDualMeasure a).measure) := by
  let μ := (realSelfDualMeasure a).measure
  exact (measurePreserving_piCongrLeft (fun _ => μ) (rightIndices k m l)).comp
    (RectangleTate.measurePreserving_uncurry (fun (_ : Fin m) (_ : Fin l) => μ))

private theorem join_stack (X : Mat k l) (Y : Mat m l) :
    joinRectangularCoordinates (inLeading k m l) (toLeading k m l X) (toComplement k m l Y) =
      stackRows k m l X Y := by
  ext i j
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · have hi : inLeading k m l (i₀.castAdd m, j) := i₀.isLt
    simp only [joinRectangularCoordinates, dite_eq_left hi, stackRows_left]
    exact toLeading_apply k m l X i₀ j
  · have hi : ¬ inLeading k m l (i₁.natAdd k, j) := by unfold inLeading; simp
    simp only [joinRectangularCoordinates, dite_eq_right hi, stackRows_right]
    exact toComplement_apply k m l Y i₁ j

private theorem pairing_leading (X H : Mat k l) :
    ∑ p : U, toLeading k m l X p * toLeading k m l H p = ∑ i, ∑ j, X i j * H i j := by
  rw [← (leftIndices k m l).sum_comp, Fintype.sum_prod_type]
  rfl

private theorem toComplement_zero : toComplement k m l (0 : Mat m l) = 0 := by
  funext j
  obtain ⟨i, rfl⟩ := (rightIndices k m l).surjective j
  exact toComplement_apply k m l 0 i.1 i.2

private theorem rectFourier_stack (a : ℝˣ) (Φ : 𝓢(Mat (k + m) l, ℂ)) (H : Mat k l) :
    rectFourier a (fun X => Φ (stackRows k m l X 0)) H =
      ∫ Y, rectFourier a Φ (stackRows k m l H Y) ∂rectangularMeasure (realSelfDualMeasure a) m l := by
  obtain ⟨-, -, h⟩ := realGodementRectangularFourier (k + m) l (inLeading k m l) a Φ
    (toLeading k m l H) (toComplement k m l (0 : Mat m l))
  rw [toComplement_zero] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, neg_zero, AddChar.map_zero_eq_one,
    mul_one] at h
  rw [← (measurePreserving_toLeading k m l a).integral_comp',
    ← (measurePreserving_toComplement k m l a).integral_comp'] at h
  rw [← toComplement_zero k m l] at h
  simp only [join_stack, pairing_leading, schwartzFourier_eq] at h
  exact h.symm

private def leadingLinear : Mat k l →ₗ[ℝ] Mat (k + m) l where
  toFun X := stackRows k m l X 0
  map_add' X Y := by
    ext i j
    refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i <;> simp
  map_smul' z X := by
    ext i j
    refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i <;> simp

private theorem leadingLinear_injective : Function.Injective (leadingLinear k m l) := by
  intro X Y h
  ext i j
  simpa only [leadingLinear, LinearMap.coe_mk, AddHom.coe_mk, stackRows_left] using
    congrArg (fun A : Mat (k + m) l => A (i.castAdd m) j) h

/-- Restriction of a rectangular Schwartz function to the leading rows after left multiplication. -/
def leadingRestriction (g : G (k + m)) (Φ : 𝓢(Mat (k + m) l, ℂ)) : 𝓢(Mat k l, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (leadingLinear k m l).toContinuousLinearMap.hasTemperateGrowth
    ((leadingLinear k m l).injective_iff_antilipschitz.mp (leadingLinear_injective k m l)).choose_spec.2
    (pullRectangle g Φ)

@[simp] theorem leadingRestriction_apply (g : G (k + m)) (Φ : 𝓢(Mat (k + m) l, ℂ)) (X : Mat k l) :
    leadingRestriction k m l g Φ X = Φ (g.val * stackRows k m l X 0) := rfl

private theorem join_complement_stack (H : Mat k l) (Y : Mat m l) :
    joinRectangularCoordinates (outLeading k m l) (toComplement k m l Y)
        (fun q => toLeading k m l H ⟨q.val, not_not.mp q.2⟩) = stackRows k m l H Y := by
  ext i j
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · have hi : ¬ outLeading k m l (i₀.castAdd m, j) := not_not.mpr i₀.isLt
    simp only [joinRectangularCoordinates, dite_eq_right hi, stackRows_left]
    exact toLeading_apply k m l H i₀ j
  · have hi : outLeading k m l (i₁.natAdd k, j) := by unfold outLeading inLeading; simp
    simp only [joinRectangularCoordinates, dite_eq_left hi, stackRows_right]
    exact toComplement_apply k m l Y i₁ j

/-- Each complementary Fourier fiber is absolutely integrable. -/
theorem integrable_rectTransform_complement (a : ℝˣ) (g : G (k + m)) (Φ : 𝓢(Mat (k + m) l, ℂ))
    (H : Mat k l) :
    Integrable (fun Y => rectTransform a Φ (g⁻¹.val.transpose * stackRows k m l H Y))
      (rectangularMeasure (realSelfDualMeasure a) m l) := by
  let gᵢ := Langlands.GeneralLinear.inverseTranspose (k + m) ℝ g
  let Ψ := pullRectangle gᵢ (rectTransform a Φ)
  obtain ⟨hf, -, -⟩ := realGodementRectangularFourier (k + m) l (outLeading k m l) a Ψ 0
    (fun q => toLeading k m l H ⟨q.val, not_not.mp q.2⟩)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, AddChar.map_zero_eq_one,
    mul_one] at hf
  have h := (measurePreserving_toComplement k m l a).integrable_comp_of_integrable hf
  have hEq : (fun Y => Ψ (joinRectangularCoordinates (outLeading k m l) (toComplement k m l Y)
        (fun q => toLeading k m l H ⟨q.val, not_not.mp q.2⟩))) =
      (fun Y => rectTransform a Φ (g⁻¹.val.transpose * stackRows k m l H Y)) := by
    funext Y
    rw [join_complement_stack]
    rfl
  exact hEq ▸ h

/-- Fourier integration in complementary rows after an invertible coordinate change. -/
def RealGapLeadingFourierStatement : Prop :=
  ∀ (a : ℝˣ) (g : G (k + m)) (Φ : 𝓢(Mat (k + m) l, ℂ)) (H : Mat k l),
    rectFourier a (leadingRestriction k m l g Φ) H =
      ((realNormalizedAbs g.val.det)⁻¹ ^ l) •
        ∫ Y, rectTransform a Φ (g⁻¹.val.transpose * stackRows k m l H Y)
          ∂rectangularMeasure (realSelfDualMeasure a) m l

theorem realGapLeadingFourier : RealGapLeadingFourierStatement k m l := by
  intro a g Φ H
  have h := rectFourier_stack k m l a (pullRectangle g Φ) H
  have hF : (leadingRestriction k m l g Φ : Mat k l → ℂ) =
      fun X => pullRectangle g Φ (stackRows k m l X 0) := rfl
  rw [hF, h]
  simp only [rectFourier_pullRectangle, rectTransform_apply, integral_smul]

end Langlands.Global.RankinSelbergGlobal.RealGapLeadingFourier
