import Langlands.Global.RankinSelberg.ComplexLocalPolynomialGaussian
import Langlands.Global.RankinSelberg.ComplexGodementStandardGrowth
import Langlands.Representation.Archimedean.ComplexLastRowIntegral

/-! # Half-strength Gaussian integrability for unitary Godement samples -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Archimedean.ComplexLastRowIntegral (sqNorm_vecMul)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (mul_conjTranspose_one)
open ComplexJacquet (complexMatrixPolynomialGaussianSchwartz
  complexMatrixPolynomialGaussianSchwartz_apply complexMatrixPolynomialGaussian
  ComplexMatrixPolynomialIndex)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel

variable {m n : ℕ}

/-- The polynomial Gaussian as a Schwartz test for the operator norm on matrices. -/
def godementPolynomialGaussian (t : ℝ) (ht : 0 < t)
    (p : MvPolynomial (ComplexMatrixPolynomialIndex m n) ℂ) :
    𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ) :=
  @SchwartzMap.compCLMOfContinuousLinearEquiv ℂ _ _ _
    Matrix.normedAddCommGroup Matrix.normedSpace _ _ _
    Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace _
    (ContinuousLinearEquiv.refl ℝ (Matrix (Fin m) (Fin n) ℂ))
    (complexMatrixPolynomialGaussianSchwartz t ht p)

theorem godementPolynomialGaussian_apply (t : ℝ) (ht : 0 < t)
    (p : MvPolynomial (ComplexMatrixPolynomialIndex m n) ℂ) (X : Matrix (Fin m) (Fin n) ℂ) :
    godementPolynomialGaussian t ht p X = complexMatrixPolynomialGaussian t p X := by
  exact complexMatrixPolynomialGaussianSchwartz_apply t ht p X

/-- The real Gaussian with exponent `-∑ |Xᵢⱼ|² / 2` as a rectangular Schwartz test. -/
def godementHalfGaussian (m n : ℕ) : 𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ) :=
  godementPolynomialGaussian (1 / 2) (by norm_num) 1

theorem godementHalfGaussian_apply (X : Matrix (Fin m) (Fin n) ℂ) :
    godementHalfGaussian m n X = (Real.exp (-(∑ i, ∑ j, ‖X i j‖ ^ 2) / 2) : ℂ) := by
  rw [godementHalfGaussian, godementPolynomialGaussian_apply]
  unfold complexMatrixPolynomialGaussian
  rw [map_one, one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  apply congrArg (fun t : ℝ => (Real.exp t : ℂ))
  change -((1 / 2 : ℝ) * (∑ i, ∑ j, ‖X i j‖ ^ 2)) = _
  ring

/-- The half-strength Gaussian is constant under right unitary translation. -/
theorem godementHalfGaussian_mul_unitary (X : Matrix (Fin m) (Fin n) ℂ)
    (k : unitaryCompact ℂ n) :
    godementHalfGaussian m n (X * k.val.val) = godementHalfGaussian m n X := by
  have h : (∑ i, ∑ j, ‖(X * k.val.val) i j‖ ^ 2) = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact sqNorm_vecMul (mul_conjTranspose_one k) (X i)
  simp only [godementHalfGaussian_apply, h]

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "U" => unitaryCompact ℂ (r + 1 + 1)
local notation "Φhalf" => godementHalfGaussian (r + 1) (r + 1 + 1)

private theorem trailingRows_unitary_gaussian (h : H) (k : U) :
    Φhalf (h.val * trailingRows k.val.val) = Φhalf (h.val * trailingRows (1 : G).val) := by
  have hrows : trailingRows k.val.val = trailingRows (1 : G).val * k.val.val := by
    conv_lhs => rw [← one_mul k.val.val]
    exact (Matrix.submatrix_mul (1 : G).val k.val.val Fin.succ id id Function.bijective_id).symm
  rw [hrows, ← Matrix.mul_assoc, godementHalfGaussian_mul_unitary _ k]

universe u

/-- In the Godement convergence half-plane the half-strength Gaussian is integrable
on any product of unitary samples and group Haar with an integrable sample weight. -/
def ComplexGodementHalfGaussianStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] (ds : List ComplexCharacterData), ds.length = r + 1 →
    ∃ M : ℕ, ∀ (d : ComplexCharacterData) (f : H → ℂ),
      f ∈ complexStandardModule (r + 1) ds →
      ((r + 1 : ℕ) : ℝ) + M ≤ (d.exponent + ((((r + 1 : ℕ) : ℂ) + 1) / 2)).re →
    ∀ (T : Type u) [MeasurableSpace T] (κ : Measure T) (w : T → ℂ), Integrable w κ →
    ∀ k : T → U,
      Integrable (fun x : T × H => w x.1 *
        godementSectionIntegrand d Φhalf f (k x.1).val x.2) (κ.prod ν)

theorem complexGodementHalfGaussian : ComplexGodementHalfGaussianStatement.{u} (r := r) := by
  intro ν _ ds hs
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace H := e.locallyCompactSpace
  let : SecondCountableTopology H := e.secondCountableTopology
  obtain ⟨M, hM⟩ := complexGodementStandardConvergence (r + 1) (Nat.succ_pos r) ds hs
  refine ⟨M, fun d f hf hd T _ κ w hw k => ?_⟩
  have h1 : Integrable (godementSectionIntegrand d Φhalf f 1) ν := by
    rw [Measure.isMulLeftInvariant_eq_smul ν (complexGeneralLinearHaar (r + 1))]
    exact (hM d Φhalf f hf hd 1).smul_measure_nnreal
  refine (hw.mul_prod h1).congr (ae_of_all _ fun x => ?_)
  exact congrArg
    (fun z => w x.1 * (z * f x.2⁻¹ *
      characterWeight d ((((r + 1 : ℕ) : ℂ) + 1) / 2) (determinant x.2)))
    (trailingRows_unitary_gaussian x.2 (k x.1)).symm

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
