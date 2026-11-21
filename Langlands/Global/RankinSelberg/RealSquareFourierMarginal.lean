import Langlands.Analysis.SchwartzFourierMarginal
import Langlands.Global.RankinSelberg.RealFourierSchwartz
import Langlands.Global.RankinSelberg.RectangleTateMeasure
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-! # Complementary triangular marginals for real matrix Fourier transformation -/

noncomputable section

open Matrix MeasureTheory WithLp
open scoped FourierTransform Matrix.Norms.Operator NNReal RealInnerProductSpace SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.RealSquareFourier

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.GeneralLinear (UpperEntryPair)
open Langlands.HarmonicAnalysis (UnitaryAdditiveCharacter)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Idx" => Fin n × Fin n
local notation "Off" => UpperEntryPair n
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "U" => EuclideanSpace ℝ Off
local notation "P" => WithLp 2 (D × WithLp 2 (U × U))

/-- The real upper triangular matrix with the given diagonal and strictly upper entries. -/
def upperTriangularEntries (d : Fin n → ℝ) (u : Off → ℝ) : Mat :=
  fun i j => if hij : i < j then u ⟨(i, j), hij⟩ else if i = j then d i else 0

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
    · simp [hij, le_of_lt hij]
  right_inv p := by
    rcases p with ⟨i, j⟩
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp
    · simp [h, not_lt_of_gt h]

private theorem card_entries : Fintype.card Idx = n + 2 * Fintype.card Off := by
  rw [← Fintype.card_congr (entryIndex (n := n))]
  simp only [Fintype.card_sum, Fintype.card_fin, two_mul]

private def curry : (Idx → ℝ) ≃L[ℝ] Mat :=
  ({ toEquiv := Equiv.curry (Fin n) (Fin n) ℝ
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : _ ≃ₗ[ℝ] _).toContinuousLinearEquiv

private abbrev coordinates (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)

private def ungroup : P ≃ₗᵢ[ℝ] EuclideanSpace ℝ Idx :=
  let e₁ := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin n ⊕ (Off ⊕ Off) => ℝ)
  let e₂ := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Off ⊕ Off => ℝ)
  ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ D) e₂.symm).trans
    e₁.symm).trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ entryIndex)

local instance squareFourierProductFiniteDimensional : FiniteDimensional ℝ P :=
  ungroup.symm.toLinearEquiv.finiteDimensional

private abbrev point (d : D) (u l : U) : P := toLp 2 (d, toLp 2 (u, l))

private abbrev assemble (d : D) (u l : U) : Mat :=
  curry (coordinates Idx (ungroup (point d u l)))

private theorem assemble_upper (d : D) (u : U) :
    assemble d u 0 = upperTriangularEntries (coordinates (Fin n) d) (coordinates Off u) := by
  ext i j
  change (Sum.elim (ofLp d) (Sum.elim (ofLp u) (ofLp (0 : U))))
      (entryIndex.symm (i, j)) = _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [entryIndex, upperTriangularEntries, h]
  · simp [entryIndex, upperTriangularEntries]
  · simp [entryIndex, upperTriangularEntries, h, not_lt_of_gt h, ne_of_gt h]

private theorem assemble_lower (d : D) (l : U) :
    assemble d 0 l = (upperTriangularEntries (coordinates (Fin n) d) (coordinates Off l))ᵀ := by
  ext i j
  change (Sum.elim (ofLp d) (Sum.elim (ofLp (0 : U)) (ofLp l)))
      (entryIndex.symm (i, j)) = _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [entryIndex, upperTriangularEntries, Matrix.transpose_apply, h, not_lt_of_gt h, ne_of_gt h]
  · simp [entryIndex, upperTriangularEntries, Matrix.transpose_apply]
  · simp [entryIndex, upperTriangularEntries, Matrix.transpose_apply, h, not_lt_of_gt h]

private def physicalSlice : WithLp 2 (D × U) →ₗᵢ[ℝ] P :=
  ({ toFun p := point (ofLp p).1 (ofLp p).2 0
     map_add' _ _ := by simp [← toLp_add]
     map_smul' _ _ := by simp [← toLp_smul] } : _ →ₗ[ℝ] _).isometryOfInner
    (fun p q => by simp [WithLp.prod_inner_apply])

private abbrev euclidean (Φ : 𝓢(Mat, ℂ)) : 𝓢(EuclideanSpace ℝ Idx, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ((coordinates Idx).trans curry) Φ

private abbrev regroup (Φ : 𝓢(Mat, ℂ)) : 𝓢(P, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ungroup.toContinuousLinearEquiv (euclidean Φ)

private def euclideanMarginal (Φ : 𝓢(Mat, ℂ)) : 𝓢(D, ℂ) :=
  Langlands.Analysis.SchwartzFourierMarginal.marginal
    (SchwartzMap.compCLMOfAntilipschitz ℂ
      physicalSlice.toContinuousLinearMap.hasTemperateGrowth
      physicalSlice.isometry.antilipschitzWith (regroup Φ))

private theorem euclideanMarginal_apply (Φ : 𝓢(Mat, ℂ)) (d : D) :
    euclideanMarginal Φ d = ∫ u : U, regroup Φ (point d u 0) := by
  rw [euclideanMarginal, Langlands.Analysis.SchwartzFourierMarginal.marginal_apply]
  rfl

/-- The scalar density of the self-dual measure with character of parameter `b`. -/
def density (b : ℝˣ) : ℝ≥0 := NNReal.sqrt ‖(b : ℝ)‖₊

private theorem density_pos (b : ℝˣ) : 0 < density b := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)

private theorem density_sq (b : ℝˣ) : (density b : ℝ) ^ 2 = |(b : ℝ)| := by
  rw [← NNReal.coe_pow, density, NNReal.sq_sqrt, coe_nnnorm, Real.norm_eq_abs]

local instance selfDualSigmaFinite (b : ℝˣ) : SigmaFinite (realSelfDualMeasure b).measure :=
  letI := (realSelfDualMeasure b).isAddHaar
  inferInstance

private theorem measure_pi_eq {ι : Type*} [Fintype ι] (b : ℝˣ) :
    Measure.pi (fun _ : ι => (realSelfDualMeasure b).measure) =
      density b ^ Fintype.card ι • (volume : Measure (ι → ℝ)) := by
  change Measure.pi (fun _ : ι => density b • (volume : Measure ℝ)) = _
  rw [RectangleTate.pi_smul_eq]
  simp only [Finset.prod_const, Finset.card_univ]
  rfl

private theorem integral_coordinates {ι : Type*} [Fintype ι] (b : ℝˣ)
    (f : EuclideanSpace ℝ ι → ℂ) :
    (∫ x : ι → ℝ, f ((coordinates ι).symm x)
        ∂Measure.pi (fun _ : ι => (realSelfDualMeasure b).measure)) =
      (density b : ℝ) ^ Fintype.card ι • ∫ x, f x := by
  rw [measure_pi_eq, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_pow]
  congr 1
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm).integral_comp'
    (f := MeasurableEquiv.toLp 2 (ι → ℝ)) f

/-- Schwartz marginal on the diagonal, integrating the supplied square matrix function over
strictly upper entries with their product self-dual measure. -/
def upperMarginal (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) : 𝓢(Fin n → ℝ, ℂ) :=
  ((density b : ℝ) ^ Fintype.card Off) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates (Fin n)).symm (euclideanMarginal Φ)

theorem upperMarginal_apply (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) (d : Fin n → ℝ) :
    upperMarginal b Φ d = ∫ u : Off → ℝ, Φ (upperTriangularEntries d u)
      ∂Measure.pi (fun _ : Off => (realSelfDualMeasure b).measure) := by
  let x : D := (coordinates (Fin n)).symm d
  calc
    _ = ((density b : ℝ) ^ Fintype.card Off) • ∫ u : U, Φ (upperTriangularEntries d (coordinates Off u)) := by
      change ((density b : ℝ) ^ Fintype.card Off) • euclideanMarginal Φ x = _
      rw [euclideanMarginal_apply]
      congr 1
      exact integral_congr_ae (ae_of_all _ fun u => congrArg Φ (assemble_upper x u))
    _ = _ := (integral_coordinates b (fun u : U => Φ (upperTriangularEntries d (coordinates Off u)))).symm

private def frequencyEquiv (ι : Type*) [Fintype ι] (b : ℝˣ) : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
  (coordinates ι).symm.trans (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (-b))

private abbrev frequency {E : Type*} [SMul ℝ E] (b : ℝˣ) (x : E) : E := -((b : ℝ)) • x

private theorem frequencyEquiv_apply {ι : Type*} [Fintype ι] (b : ℝˣ) (x : ι → ℝ) :
    frequencyEquiv ι b x = frequency b ((coordinates ι).symm x) := by
  simp [frequencyEquiv, Units.smul_def]

private def coordinateTransform {ι : Type*} [Fintype ι] (b : ℝˣ) (Φ : 𝓢(ι → ℝ, ℂ)) : 𝓢(ι → ℝ, ℂ) :=
  ((density b : ℝ) ^ Fintype.card ι) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (frequencyEquiv ι b)
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates ι) Φ))

private theorem coordinateTransform_apply {ι : Type*} [Fintype ι] (b : ℝˣ)
    (Φ : 𝓢(ι → ℝ, ℂ)) (x : ι → ℝ) :
    coordinateTransform b Φ x = ∫ y : ι → ℝ, Φ y * (realScaledCharacter b).complex (∑ i, y i * x i)
      ∂Measure.pi (fun _ : ι => (realSelfDualMeasure b).measure) := by
  rw [coordinateTransform, _root_.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, SchwartzMap.fourier_coe, Real.fourier_eq]
  calc
    _ = ((density b : ℝ) ^ Fintype.card ι) • ∫ y : EuclideanSpace ℝ ι,
        Φ (coordinates ι y) * (realScaledCharacter b).complex (∑ i, y i * x i) := by
      congr 1
      apply integral_congr_ae
      refine ae_of_all _ fun y => ?_
      simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, Circle.smul_def,
        smul_eq_mul, mul_comm (Φ _), UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply]
      congr 2
      rw [frequencyEquiv_apply, PiLp.inner_apply]
      simp only [RCLike.inner_apply, conj_trivial]
      congr 1
      change -(∑ i : ι, (-((b : ℝ)) * x i) * y i) = (b : ℝ) * ∑ i, y i * x i
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := (integral_coordinates b (fun y : EuclideanSpace ℝ ι =>
      Φ (coordinates ι y) * (realScaledCharacter b).complex (∑ i, y i * x i))).symm

private theorem coordinateTransform_eq_realFourierTransform (b : ℝˣ) (Φ : 𝓢(Fin n → ℝ, ℂ)) (x : Fin n → ℝ) :
    coordinateTransform b Φ x = realFourierTransform b Φ x := by
  rw [coordinateTransform_apply]
  rfl

/-- The square matrix Fourier transform with phase `ψ_b(Tr(XᵀY))` and the product self-dual measure. -/
def matrixTransform (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ curry.symm
    (coordinateTransform b (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ curry Φ))

theorem matrixTransform_apply (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) (X : Mat) :
    matrixTransform b Φ X = ∫ Y : Mat, Φ Y * (realScaledCharacter b).complex (Matrix.trace (Xᵀ * Y))
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => (realSelfDualMeasure b).measure)) := by
  let μ := (realSelfDualMeasure b).measure
  let f : (Idx → ℝ) → ℂ := fun y => Φ (curry y) *
    (realScaledCharacter b).complex (∑ i, y i * curry.symm X i)
  change coordinateTransform b (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ curry Φ) (curry.symm X) = _
  rw [coordinateTransform_apply]
  calc
    (∫ y, f y ∂Measure.pi (fun _ : Idx => μ)) =
        ∫ Y : Mat, f (curry.symm Y) ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)) :=
      ((RectangleTate.measurePreserving_uncurry (fun (_ _ : Fin n) => μ)).integral_comp'
        (f := (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm) f).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with Y
      let Y' : Mat := Y
      have h : (∑ i : Idx, curry.symm Y' i * curry.symm X i) = Matrix.trace (Xᵀ * Y') := by
        simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.transpose_apply]
        change (∑ i, ∑ j, Y i j * X i j) = ∑ i, ∑ j, X j i * Y j i
        rw [Finset.sum_comm]
        simp only [mul_comm]
      change Φ (curry (curry.symm Y')) * (realScaledCharacter b).complex
        (∑ i : Idx, curry.symm Y' i * curry.symm X i) =
          Φ Y' * (realScaledCharacter b).complex (Matrix.trace (Xᵀ * Y'))
      rw [ContinuousLinearEquiv.apply_symm_apply, h]

private theorem matrixTransform_assemble (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) (d : D) (u l : U) :
    matrixTransform b Φ (assemble d u l) =
      ((density b : ℝ) ^ Fintype.card Idx) •
        (𝓕 (regroup Φ) : 𝓢(P, ℂ)) (point (frequency b d) (frequency b u) (frequency b l)) := by
  have hfreq : point (frequency b d) (frequency b u) (frequency b l) = frequency b (point d u l) := rfl
  change ((density b : ℝ) ^ Fintype.card Idx) •
    (𝓕 (euclidean Φ) : 𝓢(EuclideanSpace ℝ Idx, ℂ))
      (frequencyEquiv Idx b (coordinates Idx (ungroup (point d u l)))) = _
  have hs : frequency b (ungroup (point d u l)) = ungroup (frequency b (point d u l)) :=
    (map_smul ungroup (-((b : ℝ))) (point d u l)).symm
  rw [hfreq, frequencyEquiv_apply, ContinuousLinearEquiv.symm_apply_apply, hs]
  congr 1
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact (Real.fourier_comp_linearIsometry ungroup (euclidean Φ) (frequency b (point d u l))).symm

private theorem integral_frequency (b : ℝˣ) (f : U → ℂ) :
    (∫ l : U, f (frequency b l)) = ((density b : ℝ) ^ (2 * Fintype.card Off))⁻¹ • ∫ l, f l := by
  rw [Measure.integral_comp_smul volume, pow_mul, density_sq, abs_inv, abs_pow, abs_neg]
  simp

/-- Integrating the matrix Fourier transform over the lower entries of a lower triangular slice
is the diagonal Fourier transform of the upper marginal. Both integrals use self-dual measures. -/
def RealSquareFourierMarginalStatement : Prop :=
  ∀ (b : ℝˣ) (Φ : 𝓢(Mat, ℂ)) (d : Fin n → ℝ),
    (∫ l : Off → ℝ, matrixTransform b Φ ((upperTriangularEntries d l)ᵀ)
        ∂Measure.pi (fun _ : Off => (realSelfDualMeasure b).measure)) =
      realFourierTransform b (upperMarginal b Φ) d

theorem realSquareFourierMarginal : RealSquareFourierMarginalStatement (n := n) := by
  intro b Φ d
  let c : ℝ := density b
  let x : D := (coordinates (Fin n)).symm d
  let J (l : U) : ℂ := (𝓕 (regroup Φ) : 𝓢(P, ℂ)) (point (frequency b x) 0 l)
  have hc : c ≠ 0 := NNReal.coe_ne_zero.mpr (density_pos b).ne'
  have hJ : (∫ l : U, J l) = (𝓕 (euclideanMarginal Φ)) (frequency b x) := by
    rw [SchwartzMap.fourier_coe]
    exact (Langlands.Analysis.SchwartzFourierMarginal.schwartzFourierMixedSlice
      (E := D) («U» := U) (L := U) (regroup Φ) (frequency b x)).trans
      (congrArg (fun f : D → ℂ => (𝓕 f) (frequency b x))
        (funext (euclideanMarginal_apply Φ))).symm
  calc
    _ = (c ^ Fintype.card Off) • ∫ l : U, matrixTransform b Φ (assemble x 0 l) := by
      rw [← integral_coordinates b (fun l : U => matrixTransform b Φ (assemble x 0 l))]
      apply integral_congr_ae
      exact ae_of_all _ fun l => congrArg (matrixTransform b Φ) (assemble_lower x ((coordinates Off).symm l)).symm
    _ = (c ^ Fintype.card Off) • ((c ^ Fintype.card Idx) • ∫ l : U, J (frequency b l)) := by
      congr 1
      rw [← integral_smul]
      apply integral_congr_ae
      exact ae_of_all _ fun l => by simpa only [J, smul_zero] using matrixTransform_assemble b Φ x 0 l
    _ = (c ^ n) • ((c ^ Fintype.card Off) • (𝓕 (euclideanMarginal Φ)) (frequency b x)) := by
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
    _ = coordinateTransform b (upperMarginal b Φ) d := by
      change (c ^ n) • ((c ^ Fintype.card Off) • (𝓕 (euclideanMarginal Φ)) (frequency b x)) =
        (c ^ Fintype.card (Fin n)) •
          (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates (Fin n)) (upperMarginal b Φ)))
            (frequencyEquiv (Fin n) b d)
      rw [Fintype.card_fin, frequencyEquiv_apply]
      have h :
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates (Fin n)) (upperMarginal b Φ) =
            (c ^ Fintype.card Off) • euclideanMarginal Φ := by
        ext y
        change (c ^ Fintype.card Off) • euclideanMarginal Φ ((coordinates (Fin n)).symm (coordinates (Fin n) y)) = _
        rw [ContinuousLinearEquiv.symm_apply_apply]
        rfl
      rw [h, FourierTransform.fourier_smul]
      rfl
    _ = _ := coordinateTransform_eq_realFourierTransform b (upperMarginal b Φ) d

end Langlands.Global.RankinSelbergGlobal.RealSquareFourier
