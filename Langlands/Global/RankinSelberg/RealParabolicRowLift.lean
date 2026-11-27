import Langlands.Global.RankinSelberg.RealGodementRowFourierInversion
import Langlands.Global.RankinSelberg.RealGodementFourierCovariance
import Langlands.Global.RankinSelberg.RealGodementGaussianPolynomial
import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Analysis.SchwartzScaledCutoff

/-! # The real parabolic Fourier moment on the leading block -/

noncomputable section

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open MeasureTheory Matrix
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicRowLift

open ArchimedeanLocal RealGodement
open RealGodementGaussianPolynomial (matrixSqNorm scaledGaussian scaledGaussian_apply)

variable {r p : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Row" => (Fin (r + 1) → ℝ)
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (p + 1)) ℝ
local notation "Tail" => Matrix (Fin (r + 1)) (Fin p) ℝ

private def splitColumns : Rect ≃L[ℝ] Row × Tail :=
  ({ toFun := fun X => (fun i => X i 0, X.submatrix id Fin.succ)
     invFun := fun x i => Fin.cases (x.1 i) (x.2 i)
     left_inv := by
       intro X
       ext i j
       exact Fin.cases (by rfl) (fun _ => by rfl) j
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Rect ≃ₗ[ℝ] Row × Tail).toContinuousLinearEquiv

/-- The frequency supported in the first column of the upper off-diagonal block. -/
def boundaryFrequency (y : Row) : Rect := fun i j => if j = 0 then y i else 0

private theorem splitColumns_boundary (y : Row) : splitColumns (boundaryFrequency (p := p) y) = (y, 0) := by
  apply Prod.ext
  · funext i
    change (if (0 : Fin (p + 1)) = 0 then y i else 0) = y i
    simp
  · ext i j
    change (if j.succ = 0 then y i else 0) = 0
    simp

private def boundaryLinear : Row →L[ℝ] Rect :=
  splitColumns.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Row Tail)

private theorem boundaryLinear_apply (y : Row) :
    boundaryLinear (p := p) y = boundaryFrequency y := by
  change splitColumns.symm (y, 0) = boundaryFrequency y
  rw [← splitColumns_boundary y, ContinuousLinearEquiv.symm_apply_apply]

private theorem boundaryLinear_injective : Function.Injective (boundaryLinear (r := r) (p := p)) := by
  intro y z h
  rw [boundaryLinear_apply, boundaryLinear_apply] at h
  funext i
  simpa [boundaryFrequency] using
    congrArg (fun A : Rect => A i (0 : Fin (p + 1))) h

/-- The negative rectangular Fourier transform restricted to the boundary row frequencies. -/
def rowFourierProfile (a : ℝˣ) : 𝓢(Rect, ℂ) →L[ℂ] 𝓢(Row, ℂ) :=
  let E := rectangularCoordinates (r := r + 1) (s := p + 1)
  (SchwartzMap.compCLMOfAntilipschitz ℂ boundaryLinear.hasTemperateGrowth
    (boundaryLinear.toLinearMap.injective_iff_antilipschitz.mp boundaryLinear_injective).choose_spec.2).comp
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm).comp
      ((scaledEuclideanFourierCLM (-a)).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E)))

theorem rowFourierProfile_apply (a : ℝˣ) (Φ : 𝓢(Rect, ℂ)) (y : Row) :
    rowFourierProfile a Φ y = realRectangularSchwartzFourier (-a) Φ (boundaryFrequency y) := by
  change realRectangularSchwartzFourier (-a) Φ (boundaryLinear y) = _
  rw [boundaryLinear_apply]

private def extendRow (f : 𝓢(Row, ℂ)) : 𝓢(Rect, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ splitColumns
    (ComplexGodementColumnProduct.schwartzProd (ContinuousLinearMap.fst ℝ Row Tail)
      (ContinuousLinearMap.snd ℝ Row Tail) (C := 1) zero_le_one
      (fun x => by rw [one_mul, Prod.norm_def]; exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))
      f (scaledGaussian (r + 1) p 1 one_pos))

@[simp] private theorem extendRow_boundary (f : 𝓢(Row, ℂ)) (y : Row) :
    extendRow (p := p) f (boundaryFrequency y) = f y := by
  change f (splitColumns (p := p) (boundaryFrequency y)).1 *
    scaledGaussian (r + 1) p 1 one_pos (splitColumns (boundaryFrequency y)).2 = f y
  rw [splitColumns_boundary, scaledGaussian_apply]
  simp [matrixSqNorm]

private theorem rectangularFourier_neg_comp (a : ℝˣ) (f : 𝓢(Rect, ℂ)) :
    realRectangularSchwartzFourier (-a) (realRectangularSchwartzFourier a f) = f := by
  let c := rectangularCoordinates (r := r + 1) (s := p + 1)
  change SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.symm
    (scaledEuclideanFourier (-a) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.symm
        (scaledEuclideanFourier a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c f))))) = f
  have h (v : 𝓢(EuclideanSpace ℝ (Fin (r + 1) × Fin (p + 1)), ℂ)) :
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.symm v) = v := by
    ext z
    change v (c.symm (c z)) = v z
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [h, scaledEuclideanFourier_neg_comp]
  ext X
  change f (c (c.symm X)) = f X
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem rowFourierProfile_surjective (a : ℝˣ) : Function.Surjective (rowFourierProfile (r := r) (p := p) a) := by
  intro f
  refine ⟨realRectangularSchwartzFourier a (extendRow f), ?_⟩
  ext y
  rw [rowFourierProfile_apply, rectangularFourier_neg_comp, extendRow_boundary]

/-- Profiles of compactly supported rectangle tests are dense in the full row Schwartz space. -/
def RealParabolicCompactRowProfileDensityStatement : Prop :=
  ∀ (m n : ℕ) (a : ℝˣ),
    Dense (rowFourierProfile (r := m) (p := n) a ''
      {Φ | HasCompactSupport (Φ : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ → ℂ)})

theorem realParabolicCompactRowProfileDensity : RealParabolicCompactRowProfileDensityStatement := by
  intro m n a
  exact (rowFourierProfile_surjective (r := m) (p := n) a).denseRange.dense_image
    (rowFourierProfile a).continuous Langlands.Analysis.dense_hasCompactSupport_schwartz

private def lastBasisRow : Row := Pi.single (Fin.last r) 1

private theorem pairing_boundary (Y : Rect) :
    rectangularPairing Y (boundaryFrequency lastBasisRow) = Y (Fin.last r) 0 := by
  simp [rectangularPairing, boundaryFrequency, lastBasisRow, Pi.single_apply, mul_ite]

private theorem transpose_mul_boundary (g : G) :
    g.val.transpose * boundaryFrequency (p := p) lastBasisRow =
      boundaryFrequency (fun i => g.val (Fin.last r) i) := by
  ext i j
  by_cases h : j = 0 <;> simp [Matrix.mul_apply, boundaryFrequency, lastBasisRow,
    Pi.single_apply, h, mul_ite]

/-- The translated Schwartz integrand in the split Jacquet integral, with the
negative boundary phase for the Whittaker character at scale `a`. -/
def parabolicMomentKernel (a : ℝˣ) (Φ : 𝓢(Rect, ℂ)) (g : G) (Y : Rect) : ℂ :=
  Φ ((g⁻¹).val * Y) * (realScaledCharacter (-a)).complex (Y (Fin.last r) 0)

/-- The translated compact or Schwartz rectangle moment is the row profile
at the last row, with one absolute determinant factor per column. -/
theorem parabolicMomentKernel_integral (a : ℝˣ) (Φ : 𝓢(Rect, ℂ)) (g : G) :
    let μ := Langlands.RankinSelberg.rectangularMeasure (realSelfDualMeasure a) (r + 1) (p + 1)
    Integrable (parabolicMomentKernel a Φ g) μ ∧
      (∫ Y, parabolicMomentKernel a Φ g Y ∂μ) =
        ((|g.val.det| ^ (p + 1) : ℝ) : ℂ) * rowFourierProfile a Φ (fun i => g.val (Fin.last r) i) := by
  let μ := Langlands.RankinSelberg.rectangularMeasure (realSelfDualMeasure a) (r + 1) (p + 1)
  change Integrable (parabolicMomentKernel a Φ g) μ ∧ _
  let ν := (realSelfDualMeasure a).measure
  let : ν.IsAddHaarMeasure := (realSelfDualMeasure a).isAddHaar
  let : SigmaFinite ν := inferInstance
  let : (Measure.pi fun _ : Fin (p + 1) => ν).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : μ.IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Fin (r + 1) => Measure.pi fun _ : Fin (p + 1) => ν)
  let Ψ := RealGodement.rectangularTranslate g⁻¹ (1 : Langlands.GeneralLinear (p + 1) ℝ) Φ
  have hKernel (Y : Matrix (Fin (r + 1)) (Fin (p + 1)) ℝ) : parabolicMomentKernel a Φ g Y =
      Ψ Y * (realScaledCharacter (-a)).complex (Y (Fin.last r) 0) := by
    simp only [parabolicMomentKernel, Ψ, RealGodement.rectangularTranslate_apply,
      Units.val_one, Matrix.mul_one]
  constructor
  · have h : Integrable Ψ μ := Ψ.integrable
    rw [funext hKernel]
    exact h.norm.mono'
      ((Ψ.continuous.mul ((realScaledCharacter (-a)).continuous_complex.comp
        (continuous_id.matrix_elem (Fin.last r) 0))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun Y => by simp)
  have hμ : (realSelfDualMeasure (-a)).measure = (realSelfDualMeasure a).measure := by
    simp [realSelfDualMeasure]
  have hDet : (g⁻¹).val.det = g.val.det⁻¹ := by
    change (↑(Matrix.GeneralLinearGroup.det g⁻¹) : ℝ) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  calc
    (∫ Y, parabolicMomentKernel a Φ g Y ∂μ) =
        realRectangularSchwartzFourier (-a) Ψ (boundaryFrequency lastBasisRow) := by
      rw [realRectangularSchwartzFourier_apply, rectangularFourierIntegral]
      simp only [Langlands.RankinSelberg.rectangularMeasure, hμ, μ, hKernel, pairing_boundary]
    _ = ((|g.val.det| ^ (p + 1) : ℝ) : ℂ) * rowFourierProfile a Φ (fun i => g.val (Fin.last r) i) := by
      rw [show Ψ = RealGodement.rectangularTranslate g⁻¹ (1 : Langlands.GeneralLinear (p + 1) ℝ) Φ from rfl,
        realGodementFourierCovariance, rowFourierProfile_apply]
      simp only [Units.val_one, Matrix.det_one, abs_one, one_pow, mul_one, hDet,
        abs_inv, inv_pow, inv_inv, GeneralLinear.inverseTranspose_coe, inv_one, Matrix.transpose_one,
        Matrix.mul_one, transpose_mul_boundary]

/-- The rectangle profile can realize any Schwartz function of the last row of
`g`. The Jacobian is one factor of `|det g|` for each column. -/
def RealParabolicRowLiftStatement : Prop :=
  ∀ (r p : ℕ) (a : ℝˣ) (f : 𝓢((Fin (r + 1) → ℝ), ℂ)),
    ∃ Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (p + 1)) ℝ, ℂ),
      ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
        let μ := Langlands.RankinSelberg.rectangularMeasure (realSelfDualMeasure a) (r + 1) (p + 1)
        Integrable (parabolicMomentKernel a Φ g) μ ∧
          (∫ Y, parabolicMomentKernel a Φ g Y ∂μ) =
            ((|g.val.det| ^ (p + 1) : ℝ) : ℂ) * f (fun i => g.val (Fin.last r) i)

theorem realParabolicRowLift : RealParabolicRowLiftStatement := by
  intro r p a f
  obtain ⟨Φ, hΦ⟩ := rowFourierProfile_surjective (r := r) (p := p) a f
  exact ⟨Φ, fun g => by simpa only [hΦ] using parabolicMomentKernel_integral a Φ g⟩

end Langlands.Global.RankinSelbergGlobal.RealParabolicRowLift
