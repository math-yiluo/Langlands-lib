import Langlands.Global.RankinSelberg.ComplexGodementFourier
import Langlands.Global.RankinSelberg.ComplexTraceFourier
import Langlands.Representation.GodementJacquet.ComplexMatrixHaar

/-! # Fourier exchange between a leading matrix slice and the complementary rows -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingFourier

open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure)
open Langlands.GodementJacquet (complexAbsHom coe_complexAbsHom map_complex_mul_volume)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar)
open ComplexGodementFourier (rectFourier flatM piMeasure psi merge fourier)

local notation "Mat" => fun n l => Matrix (Fin n) (Fin l) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ

private def curryRect (n l : ℕ) : (Fin n × Fin l → ℂ) ≃L[ℝ] Mat n l :=
  (ComplexGodementFourier.curryLinearEquiv (Fin n) (Fin l) ℝ ℂ).toContinuousLinearEquiv

private def flatTest {n l : ℕ} (Φ : 𝓢(Mat n l, ℂ)) : 𝓢(Fin n × Fin l → ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (curryRect n l) Φ

private theorem fourier_flat {n l : ℕ} (a : ℂˣ) (Φ : Mat n l → ℂ) (Y : Mat n l) :
    ComplexGodementFourier.fourier a (fun x => Φ (Function.curry x)) (flatM Y) = rectFourier a Φ Y := by
  let ν := (complexSelfDualMeasure a).measure
  let K (x : Fin n × Fin l → ℂ) := Φ (Function.curry x) * psi a (∑ i, x i * Y i.1 i.2)
  have h := ComplexGodementFourier.measurePreserving_uncurry (ι := Fin n) (κ := Fin l) ν
  change (∫ x, K x ∂piMeasure _ a) = _
  refine (h.integral_comp' K).symm.trans ?_
  apply integral_congr_ae
  refine ae_of_all _ fun X => ?_
  let X' : Mat n l := X
  change Φ X' * psi a (∑ p : Fin n × Fin l, X' p.1 p.2 * Y p.1 p.2) =
    Φ X' * psi a (∑ i, ∑ j, X' i j * Y i j)
  rw [Fintype.sum_prod_type]

/-- The positive complex trace transform on rectangular Schwartz functions. -/
def rectTransform {n l : ℕ} (a : ℂˣ) (Φ : 𝓢(Mat n l, ℂ)) : 𝓢(Mat n l, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (curryRect n l).symm
    (ComplexTraceFourier.transform (-a) (flatTest Φ))

@[simp] theorem rectTransform_apply {n l : ℕ} (a : ℂˣ) (Φ : 𝓢(Mat n l, ℂ)) (Y : Mat n l) :
    rectTransform a Φ Y = rectFourier a Φ Y := by
  change ComplexTraceFourier.transform (-a) (flatTest Φ) (flatM Y) = _
  rw [ComplexTraceFourier.transform_apply]
  change (∫ y, (flatTest Φ) y * psi (-a) (-∑ i, y i * flatM Y i) ∂piMeasure _ (-a)) = _
  rw [ComplexGodementFourier.piMeasure_neg]
  refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans (fourier_flat a Φ Y)
  simp only [ComplexGodementFourier.psi, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    Langlands.LocalFactor.Archimedean.complexScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg, neg_neg]
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

private theorem integral_leftMul {n l : ℕ} (a : ℂˣ) (g : G n) (F : Mat n l → ℂ) :
    (∫ X, F (g.val * X) ∂rectangularMeasure (complexSelfDualMeasure a) n l) =
      ((complexNormalizedAbs g.val.det)⁻¹ ^ l) • ∫ X, F X ∂rectangularMeasure (complexSelfDualMeasure a) n l := by
  let μ := rectangularMeasure (complexSelfDualMeasure a) n l
  let : μ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let e := (leftMul l g).toHomeomorph.toMeasurableEquiv
  have h := Langlands.HarmonicAnalysis.haarMeasure_map_rectangular (volume : Measure ℂ) complexAbsHom
    (fun _ hz => map_complex_mul_volume hz) μ g.val (1 : Mat l l) g.det_ne_zero (by simp)
  have hm : μ.map e = (complexAbsHom g.val.det ^ l)⁻¹ • μ := by
    simpa only [show (⇑e) = (fun X => g.val * X) from rfl, Matrix.mul_one, Matrix.det_one,
      map_one, one_pow, Fintype.card_fin, mul_one] using h
  change (∫ X, F (e X) ∂μ) = _
  rw [← integral_map_equiv, hm, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv,
    NNReal.coe_pow, coe_complexAbsHom, inv_pow]
  rfl

/-- Left multiplication moves to the inverse transpose in the Fourier variable. -/
theorem rectFourier_pullRectangle {n l : ℕ} (a : ℂˣ) (g : G n) (Φ : 𝓢(Mat n l, ℂ)) (Y : Mat n l) :
    rectFourier a (pullRectangle g Φ) Y = ((complexNormalizedAbs g.val.det)⁻¹ ^ l) •
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
    _ = ∫ X, K (g.val * X) ∂rectangularMeasure (complexSelfDualMeasure a) n l := by
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

private def toLeading : Mat k l ≃ᵐ (U → ℂ) :=
  (MeasurableEquiv.curry (Fin k) (Fin l) ℂ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (leftIndices k m l))

private def toComplement : Mat m l ≃ᵐ (L → ℂ) :=
  (MeasurableEquiv.curry (Fin m) (Fin l) ℂ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (rightIndices k m l))

private theorem measurePreserving_toLeading (a : ℂˣ) : MeasurePreserving (toLeading k m l)
    (rectangularMeasure (complexSelfDualMeasure a) k l) (piMeasure U a) := by
  let μ := (complexSelfDualMeasure a).measure
  exact (measurePreserving_piCongrLeft (fun _ => μ) (leftIndices k m l)).comp
    (ComplexGodementFourier.measurePreserving_uncurry μ)

private theorem measurePreserving_toComplement (a : ℂˣ) : MeasurePreserving (toComplement k m l)
    (rectangularMeasure (complexSelfDualMeasure a) m l) (piMeasure L a) := by
  let μ := (complexSelfDualMeasure a).measure
  exact (measurePreserving_piCongrLeft (fun _ => μ) (rightIndices k m l)).comp
    (ComplexGodementFourier.measurePreserving_uncurry μ)

private theorem merge_stack (X : Mat k l) (Y : Mat m l) :
    merge (inLeading k m l) (toLeading k m l X) (toComplement k m l Y) = flatM (stackRows k m l X Y) := by
  funext p
  rcases p with ⟨i, j⟩
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · have hi : inLeading k m l (i₀.castAdd m, j) := i₀.isLt
    rw [ComplexGodementFourier.merge_apply, dite_eq_left hi, flatM, stackRows_left]
    rfl
  · have hi : ¬ inLeading k m l (i₁.natAdd k, j) := by unfold inLeading; simp
    rw [ComplexGodementFourier.merge_apply, dite_eq_right hi, flatM, stackRows_right]
    have e : (rightIndices k m l) (i₁, j) = ⟨(i₁.natAdd k, j), hi⟩ := rfl
    rw [← e, toComplement, MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl

private theorem pairing_leading (X H : Mat k l) :
    ∑ p : U, toLeading k m l X p * toLeading k m l H p = ∑ i, ∑ j, X i j * H i j := by
  rw [← (leftIndices k m l).sum_comp, Fintype.sum_prod_type]
  rfl

private theorem rectFourier_stack (a : ℂˣ) (Φ : 𝓢(Mat (k + m) l, ℂ)) (H : Mat k l) :
    rectFourier a (fun X => Φ (stackRows k m l X 0)) H =
      ∫ Y, rectFourier a Φ (stackRows k m l H Y) ∂rectangularMeasure (complexSelfDualMeasure a) m l := by
  have h := ComplexGodementFourier.integral_merge_left_eq (p := inLeading k m l) (-a) (flatTest Φ)
    (toLeading k m l H) (toComplement k m l (0 : Mat m l))
  have h₀ : toComplement k m l (0 : Mat m l) = 0 := by
    funext j
    obtain ⟨i, rfl⟩ := (rightIndices k m l).surjective j
    rw [toComplement, MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  rw [h₀] at h
  simp only [neg_neg, ComplexGodementFourier.piMeasure_neg, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, AddChar.map_zero_eq_one, mul_one] at h
  rw [← (measurePreserving_toLeading k m l a).integral_comp',
    ← (measurePreserving_toComplement k m l a).integral_comp'] at h
  simp only [← h₀, merge_stack, pairing_leading] at h
  exact h.trans (integral_congr_ae (ae_of_all _ fun Y => fourier_flat a Φ (stackRows k m l H Y)))

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

/-- Each complementary Fourier fiber is absolutely integrable. -/
theorem integrable_rectTransform_complement (a : ℂˣ) (g : G (k + m)) (Φ : 𝓢(Mat (k + m) l, ℂ))
    (H : Mat k l) :
    Integrable (fun Y => rectTransform a Φ (g⁻¹.val.transpose * stackRows k m l H Y))
      (rectangularMeasure (complexSelfDualMeasure a) m l) := by
  let gᵢ := Langlands.GeneralLinear.inverseTranspose (k + m) ℂ g
  let Ψ := flatTest (pullRectangle gᵢ (rectTransform a Φ))
  let f (y : L → ℂ) := Ψ (merge (inLeading k m l) (toLeading k m l H) y)
  have hf : Integrable f (piMeasure L a) := by
    refine ComplexGodementFourier.integrable_of_norm_le_schwartz _ Ψ (g := _) ?_ ?_ fun y => le_rfl
    · apply Continuous.aestronglyMeasurable
      exact Ψ.continuous.comp ((ComplexGodementFourier.continuous_merge (inLeading k m l)).comp
        (continuous_const.prodMk continuous_id))
    · exact ComplexGodementFourier.norm_le_norm_merge_right (inLeading k m l) (toLeading k m l H)
  have h := (measurePreserving_toComplement k m l a).integrable_comp_of_integrable hf
  have hEq : (fun Y => f (toComplement k m l Y)) =
      (fun Y => rectTransform a Φ (g⁻¹.val.transpose * stackRows k m l H Y)) := by
    funext Y
    unfold f
    rw [merge_stack]
    rfl
  exact hEq ▸ h

/-- Fourier integration in complementary rows after an invertible coordinate change. -/
def ComplexGapLeadingFourierStatement : Prop :=
  ∀ (a : ℂˣ) (g : G (k + m)) (Φ : 𝓢(Mat (k + m) l, ℂ)) (H : Mat k l),
    rectFourier a (leadingRestriction k m l g Φ) H =
      ((complexNormalizedAbs g.val.det)⁻¹ ^ l) •
        ∫ Y, rectTransform a Φ (g⁻¹.val.transpose * stackRows k m l H Y)
          ∂rectangularMeasure (complexSelfDualMeasure a) m l

theorem complexGapLeadingFourier : ComplexGapLeadingFourierStatement k m l := by
  intro a g Φ H
  have h := rectFourier_stack k m l a (pullRectangle g Φ) H
  have hF : (leadingRestriction k m l g Φ : Mat k l → ℂ) =
      fun X => pullRectangle g Φ (stackRows k m l X 0) := rfl
  rw [hF, h]
  simp only [rectFourier_pullRectangle, rectTransform_apply, integral_smul]

end Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingFourier
