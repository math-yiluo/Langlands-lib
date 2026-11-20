import Langlands.Analysis.SchwartzFourierMarginal
import Langlands.Global.RankinSelberg.ComplexGodementTriangularEntries
import Langlands.Global.RankinSelberg.ComplexTraceFourier
import Langlands.Global.RankinSelberg.RectangleTateMeasure

/-! # Complementary triangular marginals for complex matrix Fourier transformation -/

noncomputable section

open Matrix MeasureTheory WithLp
open scoped ENNReal FourierTransform Matrix.Norms.Operator NNReal RealInnerProductSpace SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareFourier

open ArchimedeanLocal ComplexGodement ComplexTraceFourier
open Langlands.GeneralLinear (UpperEntryPair)
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Idx" => Fin n × Fin n
local notation "Off" => UpperEntryPair n
local notation "D" => Coordinates (Fin n)
local notation "U" => Coordinates Off
local notation "P" => WithLp 2 (D × WithLp 2 (U × U))

private def entryIndex : (Fin n ⊕ (Off ⊕ Off)) ≃ Idx where
  toFun
    | .inl i => (i, i)
    | .inr (.inl p) => p.val
    | .inr (.inr p) => p.val.swap
  invFun p :=
    if h : p.1 < p.2 then .inr (.inl ⟨p, h⟩)
    else if h' : p.2 < p.1 then .inr (.inr ⟨p.swap, h'⟩)
    else .inl p.1
  left_inv p := by
    rcases p with i | (⟨⟨i, j⟩, hij⟩ | ⟨⟨i, j⟩, hij⟩)
    · simp
    · simp [hij]
    · simp [hij, not_lt_of_gt hij]
  right_inv p := by
    rcases p with ⟨i, j⟩
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp
    · simp [h, not_lt_of_gt h]

private theorem card_entries :
    Fintype.card Idx = n + 2 * Fintype.card Off := by
  rw [← Fintype.card_congr (entryIndex (n := n))]
  simp only [Fintype.card_sum, Fintype.card_fin, two_mul]

private def curry : (Idx → ℂ) ≃L[ℝ] Mat :=
  ({ toEquiv := Equiv.curry (Fin n) (Fin n) ℂ
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : _ ≃ₗ[ℝ] _).toContinuousLinearEquiv

private def ungroup : P ≃ₗᵢ[ℝ] Coordinates Idx :=
  let e₁ := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin n ⊕ (Off ⊕ Off) => ℂ)
  let e₂ := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Off ⊕ Off => ℂ)
  ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ D) e₂.symm).trans
    e₁.symm).trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ entryIndex)

local instance squareFourierProductFiniteDimensional : FiniteDimensional ℝ P :=
  ungroup.symm.toLinearEquiv.finiteDimensional

private abbrev point (d : D) (u l : U) : P := toLp 2 (d, toLp 2 (u, l))

private abbrev assemble (d : D) (u l : U) : Mat :=
  curry (coordinates (ungroup (point d u l)))

private theorem assemble_upper (d : D) (u : U) :
    assemble d u 0 = upperTriangularEntries (coordinates d) (coordinates u) := by
  ext i j
  change (Sum.elim (ofLp d) (Sum.elim (ofLp u) (ofLp (0 : U))))
      (entryIndex.symm (i, j)) = _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [entryIndex, upperTriangularEntries, h]
  · simp [entryIndex, upperTriangularEntries]
  · simp [entryIndex, upperTriangularEntries, h, not_lt_of_gt h, ne_of_gt h]

private theorem assemble_lower (d : D) (l : U) :
    assemble d 0 l = (upperTriangularEntries (coordinates d) (coordinates l))ᵀ := by
  ext i j
  change (Sum.elim (ofLp d) (Sum.elim (ofLp (0 : U)) (ofLp l)))
      (entryIndex.symm (i, j)) = _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [entryIndex, upperTriangularEntries, Matrix.transpose_apply, h, not_lt_of_gt h, ne_of_gt h]
  · simp [entryIndex, upperTriangularEntries]
  · simp [entryIndex, upperTriangularEntries, Matrix.transpose_apply, h, not_lt_of_gt h]

private theorem ungroup_frequency (a : ℂˣ) (d : D) (u l : U) :
    frequency a (ungroup (point d u l)) =
      ungroup (point (frequency a d) (frequency a u) (frequency a l)) := by
  ext p
  rw [frequency_apply]
  change starRingEnd ℂ (2 * (a : ℂ) *
    Sum.elim (ofLp d) (Sum.elim (ofLp u) (ofLp l)) (entryIndex.symm p)) =
    Sum.elim (ofLp (frequency a d))
      (Sum.elim (ofLp (frequency a u)) (ofLp (frequency a l))) (entryIndex.symm p)
  rcases entryIndex.symm p with i | (i | i) <;> simp

private def physicalSlice : WithLp 2 (D × U) →ₗᵢ[ℝ] P :=
  ({ toFun p := point (ofLp p).1 (ofLp p).2 0
     map_add' _ _ := by simp [← toLp_add]
     map_smul' _ _ := by simp [← toLp_smul] } : _ →ₗ[ℝ] _).isometryOfInner
    (fun p q => by simp [WithLp.prod_inner_apply])

private abbrev euclidean (Φ : 𝓢(Mat, ℂ)) : 𝓢(Coordinates Idx, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates.trans curry) Φ

private abbrev regroup (Φ : 𝓢(Mat, ℂ)) : 𝓢(P, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ungroup.toContinuousLinearEquiv (euclidean Φ)

private def realMarginal (Φ : 𝓢(Mat, ℂ)) : 𝓢(D, ℂ) :=
  Langlands.Analysis.SchwartzFourierMarginal.marginal
    (SchwartzMap.compCLMOfAntilipschitz ℂ
      physicalSlice.toContinuousLinearMap.hasTemperateGrowth
      physicalSlice.isometry.antilipschitzWith (regroup Φ))

private theorem realMarginal_apply (Φ : 𝓢(Mat, ℂ)) (d : D) :
    realMarginal Φ d = ∫ u : U, regroup Φ (point d u 0) := by
  rw [realMarginal, Langlands.Analysis.SchwartzFourierMarginal.marginal_apply]
  rfl

private theorem integral_coordinates {ι : Type*} [Fintype ι] (a : ℂˣ)
    (f : Coordinates ι → ℂ) :
    (∫ x : ι → ℂ, f (coordinates.symm x)
        ∂Measure.pi (fun _ : ι => (complexSelfDualMeasure a).measure)) =
      (scale a : ℝ) ^ Fintype.card ι • ∫ x, f x := by
  rw [product_measure_eq, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_pow]
  congr 1
  exact (coordinates_measurePreserving.symm (MeasurableEquiv.toLp 2 (ι → ℂ)).symm).integral_comp'
    (f := MeasurableEquiv.toLp 2 (ι → ℂ)) f

/-- Marginal of a square matrix Schwartz test along the strictly upper entries of the upper
triangular slice, using the self-dual additive measure in each integrated entry. -/
def upperMarginal (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) : 𝓢(Fin n → ℂ, ℂ) :=
  ((scale a : ℝ) ^ Fintype.card Off) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates.symm (realMarginal Φ)

theorem upperMarginal_apply (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (d : Fin n → ℂ) :
    upperMarginal a Φ d = ∫ u : Off → ℂ, Φ (upperTriangularEntries d u)
      ∂Measure.pi (fun _ : Off => (complexSelfDualMeasure a).measure) := by
  calc
    _ = ((scale a : ℝ) ^ Fintype.card Off) •
        ∫ u : U, Φ (upperTriangularEntries d (coordinates u)) := by
      change ((scale a : ℝ) ^ Fintype.card Off) • realMarginal Φ (coordinates.symm d) = _
      rw [realMarginal_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      exact congrArg Φ (assemble_upper (coordinates.symm d) u)
    _ = _ := (integral_coordinates a (fun u => Φ (upperTriangularEntries d (coordinates u)))).symm

/-- Jacquet's square matrix Fourier transform, with self-dual measure in every entry. -/
def matrixTransform (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ curry.symm
    (transform a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ curry Φ))

theorem matrixTransform_apply (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (X : Mat) :
    matrixTransform a Φ X = ∫ Y : Mat, Φ Y *
      (complexScaledCharacter a).complex (-Matrix.trace (Xᵀ * Y))
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => (complexSelfDualMeasure a).measure)) := by
  let μ := (complexSelfDualMeasure a).measure
  let K : (Idx → ℂ) → ℂ := fun y => Φ (curry y) *
    (complexScaledCharacter a).complex (-∑ p, y p * curry.symm X p)
  change transform a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ curry Φ) (curry.symm X) = _
  rw [transform_apply a _ _]
  calc
    (∫ y, K y ∂Measure.pi (fun _ : Idx => μ)) =
        ∫ Y : Mat, K (curry.symm Y) ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)) :=
      ((RectangleTate.measurePreserving_uncurry (fun (_ _ : Fin n) => μ)).integral_comp'
        (f := (MeasurableEquiv.curry (Fin n) (Fin n) ℂ).symm) K).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with Y
      let Y' : Mat := Y
      have h : (∑ p : Idx, curry.symm Y' p * curry.symm X p) = Matrix.trace (Xᵀ * Y') := by
        simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.transpose_apply]
        change (∑ i, ∑ j, Y i j * X i j) = ∑ i, ∑ j, X j i * Y j i
        rw [Finset.sum_comm]
        simp only [mul_comm]
      change Φ (curry (curry.symm Y')) *
          (complexScaledCharacter a).complex (-∑ p, curry.symm Y' p * curry.symm X p) =
        Φ Y' * (complexScaledCharacter a).complex (-Matrix.trace (Xᵀ * Y'))
      rw [ContinuousLinearEquiv.apply_symm_apply, h]

private theorem matrixTransform_assemble (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (d : D) (u l : U) :
    matrixTransform a Φ (assemble d u l) =
      ((scale a : ℝ) ^ Fintype.card Idx) •
        (𝓕 (regroup Φ) : 𝓢(P, ℂ)) (point (frequency a d) (frequency a u) (frequency a l)) := by
  change ((scale a : ℝ) ^ Fintype.card Idx) •
    (𝓕 (euclidean Φ)) (frequency a (ungroup (point d u l))) = _
  rw [ungroup_frequency a d u l]
  congr 1
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact (Real.fourier_comp_linearIsometry ungroup (euclidean Φ)
    (point (frequency a d) (frequency a u) (frequency a l))).symm

/-- The lower triangular marginal of the square matrix transform is the finite complex
trace transform of the upper triangular marginal. Both marginals have self-dual measures. -/
def ComplexSquareFourierMarginalStatement : Prop :=
  ∀ (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (d : Fin n → ℂ),
    (∫ l : Off → ℂ, matrixTransform a Φ ((upperTriangularEntries d l)ᵀ)
        ∂Measure.pi (fun _ : Off => (complexSelfDualMeasure a).measure)) =
      transform a (upperMarginal a Φ) d

theorem complexSquareFourierMarginal : ComplexSquareFourierMarginalStatement (n := n) := by
  intro a Φ d
  let c : ℝ := scale a
  let x : D := coordinates.symm d
  let J (l : U) : ℂ := (𝓕 (regroup Φ) : 𝓢(P, ℂ)) (point (frequency a x) 0 l)
  have hc : c ≠ 0 := NNReal.coe_ne_zero.mpr (scale_pos a).ne'
  have hJ : (∫ l : U, J l) = (𝓕 (realMarginal Φ)) (frequency a x) := by
    rw [SchwartzMap.fourier_coe]
    exact (Langlands.Analysis.SchwartzFourierMarginal.schwartzFourierMixedSlice
      (E := D) («U» := U) (L := U) (regroup Φ) (frequency a x)).trans
      (congrArg (fun f : D → ℂ => (𝓕 f) (frequency a x))
        (funext (realMarginal_apply Φ))).symm
  calc
    _ = (c ^ Fintype.card Off) • ∫ l : U, matrixTransform a Φ (assemble x 0 l) := by
      rw [← integral_coordinates a (fun l : U => matrixTransform a Φ (assemble x 0 l))]
      apply integral_congr_ae
      filter_upwards with l
      exact congrArg (matrixTransform a Φ) (assemble_lower x (coordinates.symm l)).symm
    _ = (c ^ Fintype.card Off) •
          ((c ^ Fintype.card Idx) • ∫ l : U, J (frequency a l)) := by
      congr 1
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with l
      simpa only [J, map_zero] using matrixTransform_assemble a Φ x 0 l
    _ = (c ^ n) • ((c ^ Fintype.card Off) • (𝓕 (realMarginal Φ)) (frequency a x)) := by
      rw [integral_frequency, hJ]
      simp only [← smul_assoc, smul_eq_mul]
      congr 1
      change c ^ Fintype.card Off * (c ^ Fintype.card Idx *
        (c ^ (2 * Fintype.card Off))⁻¹) = c ^ n * c ^ Fintype.card Off
      rw [card_entries, pow_add]
      calc
        _ = (c ^ n * c ^ Fintype.card Off) *
            (c ^ (2 * Fintype.card Off) * (c ^ (2 * Fintype.card Off))⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hc), mul_one]
    _ = transform a (upperMarginal a Φ) d := by
      change (c ^ n) • ((c ^ Fintype.card Off) • (𝓕 (realMarginal Φ)) (frequency a x)) =
        (c ^ Fintype.card (Fin n)) •
          (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates (upperMarginal a Φ)))
            (frequency a x)
      rw [Fintype.card_fin]
      have h :
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates (upperMarginal a Φ) =
            (c ^ Fintype.card Off) • realMarginal Φ := by
        ext y
        change (c ^ Fintype.card Off) • realMarginal Φ (coordinates.symm (coordinates y)) = _
        rw [ContinuousLinearEquiv.symm_apply_apply]
        rfl
      rw [h, FourierTransform.fourier_smul]
      rfl

end Langlands.Global.RankinSelbergGlobal.ComplexSquareFourier
