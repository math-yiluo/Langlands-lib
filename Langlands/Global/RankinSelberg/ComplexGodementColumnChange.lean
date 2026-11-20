import Langlands.Global.RankinSelberg.ComplexGodementWhittakerIntegral
import Langlands.HarmonicAnalysis.RectangularFourier

/-! # The column change of variables in the complex Godement Whittaker integral -/

noncomputable section

open MeasureTheory Function
open scoped Classical Matrix.Norms.Elementwise SchwartzMap ENNReal
open Langlands.Archimedean.ComplexPartialJacquet (vecMulEquiv vecMulEquiv_apply
  vecMulLinearEquiv det_vecMulLinearEquiv)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.HarmonicAnalysis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementColumnChange

open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodementWhittaker (augmentedPoint kernelBase complexGodementWhittakerIntegral)

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "Square" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

private theorem detAbs_pos (h : G) : 0 < complexNormalizedAbs h.val.det :=
  pow_pos (norm_pos_iff.mpr h.det_ne_zero) _

private theorem det_transpose_ne_zero (h : G) : h.val.transpose.det ≠ 0 :=
  Matrix.det_transpose h.val ▸ h.det_ne_zero

private def columnEquiv (h : G) : Vec ≃ᵐ Vec := vecMulEquiv (det_transpose_ne_zero h)

private theorem columnEquiv_apply (h : G) (v : Vec) : columnEquiv h v = h.val.mulVec v := by
  rw [columnEquiv, vecMulEquiv_apply, Matrix.vecMul_transpose]

private theorem map_columnEquiv (μ : Measure Vec) [μ.IsAddHaarMeasure] (h : G) :
    μ.map (columnEquiv h) = ENNReal.ofReal ((complexNormalizedAbs h.val.det)⁻¹) • μ := by
  let e : Vec ≃ₗ[ℂ] Vec := vecMulLinearEquiv (det_transpose_ne_zero h)
  let f : Vec →ₗ[ℝ] Vec := e.restrictScalars ℝ
  have hd : LinearMap.det f = Complex.normSq h.val.det := by
    have he := LinearMap.det_restrictScalars (R := ℝ) (S := ℂ) (A := Vec) (f := (e : Vec →ₗ[ℂ] Vec))
    change LinearMap.det f = Algebra.norm ℝ (LinearMap.det (e : Vec →ₗ[ℂ] Vec)) at he
    rw [Algebra.norm_complex_apply, det_vecMulLinearEquiv (det_transpose_ne_zero h),
      Matrix.det_transpose] at he
    exact he
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := μ) (f := f)
    (by rw [hd]; exact (Complex.normSq_pos.mpr h.det_ne_zero).ne')
  rw [hd, Complex.normSq_eq_norm_sq, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))] at hmap
  exact hmap

private def inverseLastRow (h : G) : Vec := h⁻¹.val (Fin.last r)

private theorem pairing_columnEquiv (h : G) (v : Vec) :
    (∑ i, inverseLastRow h i * columnEquiv h v i) = v (Fin.last r) := by
  rw [columnEquiv_apply]
  change (h⁻¹.val.mulVec (h.val.mulVec v)) (Fin.last r) = _
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem augmentedPoint_eq_join (h : G) :
    augmentedPoint h = rectangularJoin h.val (inverseLastRow h) := rfl

/-- The inner integral of (7.6) before moving the smaller group variable into the frequency. -/
def columnIntegral (ψ : UnitaryAdditiveCharacter ℂ) (μ : AdditiveHaarMeasure ℂ)
    (Φ : Rect → ℂ) (h : G) : ℂ :=
  ∫ v, Φ (rectangularJoin h.val (h.val.mulVec v)) * ψ.complex (v (Fin.last r)) ∂rowMeasure μ (r + 1)

/-- The column Jacobian and the inverse-transpose frequency in (7.7). -/
theorem columnIntegral_eq (ψ : UnitaryAdditiveCharacter ℂ) (μ : AdditiveHaarMeasure ℂ)
    (Φ : Rect → ℂ) (h : G) :
    columnIntegral ψ μ Φ h = ((complexNormalizedAbs h.val.det)⁻¹ : ℝ) •
      partialFourierPlusIntegral ψ μ Φ (augmentedPoint h) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  let ν := rowMeasure μ (r + 1)
  let f : Vec → ℂ := fun u => Φ (rectangularJoin h.val u) * ψ.complex (∑ i, inverseLastRow h i * u i)
  have he (v : Vec) : f (columnEquiv h v) =
      Φ (rectangularJoin h.val (h.val.mulVec v)) * ψ.complex (v (Fin.last r)) := by
    dsimp only [f]
    rw [pairing_columnEquiv, columnEquiv_apply]
  calc
    _ = ∫ v, f (columnEquiv h v) ∂ν := by
      unfold columnIntegral
      simp only [he]
      rfl
    _ = ∫ u, f u ∂ν.map (columnEquiv h) := (integral_map_equiv (columnEquiv h) f).symm
    _ = _ := by
      rw [map_columnEquiv, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (detAbs_pos h).le),
        augmentedPoint_eq_join, partialFourierPlusIntegral_join]

private def columnInclusion : Vec →ₗ[ℝ] Rect where
  toFun v := rectangularJoin 0 v
  map_add' v w := by
    ext i j
    induction j using Fin.lastCases <;> simp
  map_smul' c v := by
    ext i j
    induction j using Fin.lastCases <;> simp

private def schwartzSlice (X : Square) (Φ : 𝓢(Rect, ℂ)) : 𝓢(Vec, ℂ) := by
  have hjoin : (fun u => rectangularJoin X u) =
      fun u => rectangularJoin X 0 + columnInclusion u := by
    funext u
    ext i j
    induction j using Fin.lastCases <;> simp [columnInclusion]
  have h : (fun u => rectangularJoin X u).HasTemperateGrowth := by
    rw [hjoin]
    exact (HasTemperateGrowth.const _).add columnInclusion.toContinuousLinearMap.hasTemperateGrowth
  refine SchwartzMap.compCLM ℂ h ⟨1, 1, fun u => ?_⟩ Φ
  rw [pow_one, one_mul]
  have hu : ‖u‖ ≤ ‖rectangularJoin X u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← rectangularJoin_last X u i]
    exact Matrix.norm_entry_le_entrywise_sup_norm _
  exact hu.trans (le_add_of_nonneg_left zero_le_one)

private theorem schwartzSlice_apply (X : Square) (Φ : 𝓢(Rect, ℂ)) (u : Vec) :
    schwartzSlice X Φ u = Φ (rectangularJoin X u) := rfl

/-- Schwartz input ensures absolute convergence of each inner column integral in (7.6). -/
theorem integrable_column (ψ : UnitaryAdditiveCharacter ℂ) (μ : AdditiveHaarMeasure ℂ)
    (Φ : 𝓢(Rect, ℂ)) (h : G) :
    Integrable (fun v => Φ (rectangularJoin h.val (h.val.mulVec v)) * ψ.complex (v (Fin.last r)))
      (rowMeasure μ (r + 1)) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  let ν := rowMeasure μ (r + 1)
  let f : Vec → ℂ := fun u => schwartzSlice h.val Φ u * ψ.complex (∑ i, inverseLastRow h i * u i)
  have hf : Integrable f ν := by
    have hΦ : Integrable (schwartzSlice h.val Φ) ν := (schwartzSlice h.val Φ).integrable
    refine hΦ.norm.mono' ?_ (ae_of_all _ fun u => ?_)
    · exact ((schwartzSlice h.val Φ).continuous.mul (ψ.continuous_complex.comp
        (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)))).aestronglyMeasurable
    · simp only [f, norm_mul, UnitaryAdditiveCharacter.norm_complex, mul_one]
      exact le_rfl
  have hh : Integrable f (ν.map (columnEquiv h)) := by
    rw [map_columnEquiv]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  refine ((integrable_map_equiv (columnEquiv h) f).mp hh).congr (ae_of_all _ fun v => ?_)
  change f (columnEquiv h v) = _
  dsimp only [f]
  rw [pairing_columnEquiv, columnEquiv_apply, schwartzSlice_apply]

private theorem inv_abs_mul_detPower (h : G) (s : ℂ) :
    (((complexNormalizedAbs h.val.det)⁻¹ : ℝ) : ℂ) * ArchimedeanLocal.detPower complexNormalizedAbs h s =
      ArchimedeanLocal.detPower complexNormalizedAbs h (s - 1) := by
  unfold ArchimedeanLocal.detPower
  rw [sub_mul, Complex.exp_sub, one_mul, ← Complex.ofReal_exp, Real.exp_log (detAbs_pos h),
    div_eq_mul_inv, Complex.ofReal_inv, mul_comm]

/-- The iterated kernel of (7.6), with the determinant exponent on the smaller group. -/
def iteratedKernel (ψ : UnitaryAdditiveCharacter ℂ) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (Φ : Rect → ℂ) (W : G → ℂ) (s : ℂ) (h : G) : ℂ :=
  columnIntegral ψ μ Φ h * W h⁻¹ * (d.character (GeneralLinear.determinant h) : ℂ) *
    ArchimedeanLocal.detPower complexNormalizedAbs h s

/-- Rewriting the iterated kernel through its transformed test shifts the exponent by one. -/
theorem iteratedKernel_eq (ψ : UnitaryAdditiveCharacter ℂ) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (Φ : Rect → ℂ) (P : 𝓢(Rect, ℂ))
    (hP : ∀ X, P X = partialFourierPlusIntegral ψ μ Φ X) (W : G → ℂ) (s : ℂ) (h : G) :
    iteratedKernel ψ μ d Φ W s h = kernelBase d P W h * ArchimedeanLocal.detPower complexNormalizedAbs h (s - 1) := by
  rw [iteratedKernel, columnIntegral_eq, Complex.real_smul, ← hP, kernelBase, ← inv_abs_mul_detPower h s]
  ring

/-- On exact smaller-rank model vectors, rewriting the inner column integral gives an absolutely
convergent entire outer integral when the partially transformed test is Schwartz. -/
def ComplexGodementColumnChangeStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (ν : Measure (Langlands.GeneralLinear (r + 1) ℂ)), ν.IsHaarMeasure →
  ∀ (ψ : UnitaryAdditiveCharacter ℂ) (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (Φ : Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ → ℂ)
    (P : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ, ℂ)),
    (∀ X, P X = partialFourierPlusIntegral ψ μ Φ X) →
    ∀ (W : complexWhittakerModel r ds a),
      (∀ s, Integrable (iteratedKernel ψ μ d Φ W.val s) ν) ∧
        Differentiable ℂ (fun s => ∫ h, iteratedKernel ψ μ d Φ W.val s h ∂ν)

theorem complexGodementColumnChange : ComplexGodementColumnChangeStatement := by
  intro r ds a ν hν ψ μ d Φ P hP W
  obtain ⟨hI, hD⟩ := complexGodementWhittakerIntegral r ds a ν hν d P W
  have he (s : ℂ) : iteratedKernel ψ μ d Φ W.val s =
      fun h => kernelBase d P W.val h * ArchimedeanLocal.detPower complexNormalizedAbs h (s - 1) :=
    funext (iteratedKernel_eq ψ μ d Φ P hP W.val s)
  simp_rw [he]
  exact ⟨fun s => hI (s - 1), hD.comp (differentiable_id.sub_const 1)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodementColumnChange
