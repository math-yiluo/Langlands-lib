import Langlands.Representation.Archimedean.TransposePairing
import Langlands.Group.GL.Maps
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.DenseEmbedding

/-! # Restriction of inverse-transpose pairings to a dense algebraic module -/

noncomputable section
universe uV uE
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable (𝕂 : Type) [RCLike 𝕂] (n : ℕ)

/-- The actual matrix exponential, with its inverse, in `GL_n(𝕂)`. -/
def matrixExponentialGL (X : Matrix (Fin n) (Fin n) 𝕂) : Langlands.GeneralLinear n 𝕂 where
  val := NormedSpace.exp X
  inv := NormedSpace.exp (-X)
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

@[simp]
theorem matrixExponentialGL_coe (X : Matrix (Fin n) (Fin n) 𝕂) :
    (matrixExponentialGL 𝕂 n X : Matrix (Fin n) (Fin n) 𝕂) = NormedSpace.exp X := rfl

@[simp]
theorem matrixExponentialGL_inv (X : Matrix (Fin n) (Fin n) 𝕂) :
    (matrixExponentialGL 𝕂 n X)⁻¹ = matrixExponentialGL 𝕂 n (-X) := by
  apply Units.ext
  rfl

@[simp]
theorem inverseTranspose_matrixExponentialGL (X : Matrix (Fin n) (Fin n) 𝕂) :
    Langlands.GeneralLinear.inverseTranspose n 𝕂 (matrixExponentialGL 𝕂 n X) =
      matrixExponentialGL 𝕂 n (-X.transpose) := by
  apply Units.ext
  change (NormedSpace.exp (-X)).transpose = NormedSpace.exp (-X.transpose)
  rw [← Matrix.exp_transpose, Matrix.transpose_neg]

@[simp]
theorem inverseTranspose_unitaryToUnits (k : Matrix.unitaryGroup (Fin n) 𝕂) :
    Langlands.GeneralLinear.inverseTranspose n 𝕂 (Unitary.toUnits k) =
      Unitary.toUnits (compactIota 𝕂 n k) := by
  apply Units.ext
  rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {E : Type uE} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) 𝕂) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (R : Representation ℂ (Langlands.GeneralLinear n 𝕂) E) (e : V →ₗ[ℂ] E)

/-- The part of a dense smooth realization needed to restrict an invariant pairing.
The derivative comparison is scalar, along actual matrix exponentials, for every
continuous linear functional on the ambient space. -/
def IsDenseWeakGLRealization : Prop :=
  Function.Injective e ∧ DenseRange e ∧
  (∀ (k : Matrix.unitaryGroup (Fin n) 𝕂) (v : V),
    e (ρ k v) = R (Unitary.toUnits k) (e v)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) 𝕂) (v : V) (ℓ : E →ₗ[ℂ] ℂ), Continuous ℓ →
    HasDerivAt (fun t : ℝ => ℓ (R (matrixExponentialGL 𝕂 n (t • X)) (e v)))
      (ℓ (e (π (1 ⊗ₜ[ℝ] X) v))) 0

/-- Restriction of both arguments of an ambient bilinear form. -/
def restrictRealizationPairing (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) : V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  B.compl₁₂ e e

omit [TopologicalSpace E] in
@[simp]
theorem restrictRealizationPairing_apply (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) (y x : V) :
    restrictRealizationPairing e B y x = B (e y) (e x) := rfl

/-- Separate continuity and density prevent a nonzero ambient form from becoming
zero on the algebraic module. -/
theorem restrictRealizationPairing_ne_zero (hd : DenseRange e)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hc₁ : ∀ x : E, Continuous fun y : E => B y x)
    (hc₂ : ∀ y : E, Continuous (B y)) (hne : B ≠ 0) :
    restrictRealizationPairing e B ≠ 0 := by
  intro hz
  have hz₀ (y x : V) : B (e y) (e x) = 0 := by
    have h := LinearMap.congr_fun (LinearMap.congr_fun hz y) x
    exact h
  have hz₁ (y : V) (x : E) : B (e y) x = 0 := by
    exact congr_fun (hd.equalizer (hc₂ (e y)) continuous_const
      (funext fun v => hz₀ y v)) x
  apply hne
  ext y x
  exact congr_fun (hd.equalizer (hc₁ x) continuous_const (funext fun v => hz₁ v x)) y

/-- Restriction preserves the actual compact and complexified Lie invariance.
The Lie identity is obtained by differentiating an equality with just one moving
argument on each side, and then extending complex linearly. -/
theorem isTransposeInvariantGKPairing_restrict
    (hr : IsDenseWeakGLRealization 𝕂 n ρ π R e)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hc₁ : ∀ x : E, Continuous fun y : E => B y x)
    (hc₂ : ∀ y : E, Continuous (B y))
    (hB : ∀ (g : Langlands.GeneralLinear n 𝕂) (y x : E),
      B (R g y) (R (Langlands.GeneralLinear.inverseTranspose n 𝕂 g) x) = B y x) :
    IsTransposeInvariantGKPairing 𝕂 n ρ π (restrictRealizationPairing e B) := by
  refine ⟨?_, ?_⟩
  · intro k y x
    simp only [restrictRealizationPairing_apply, hr.2.2.1]
    rw [← inverseTranspose_unitaryToUnits]
    exact hB _ _ _
  · have hreal (X : Matrix (Fin n) (Fin n) 𝕂) (y x : V) :
        B (e (π (1 ⊗ₜ[ℝ] X) y)) (e x) =
          B (e y) (e (π (1 ⊗ₜ[ℝ] X.transpose) x)) := by
      have hy := hr.2.2.2 X y (B.flip (e x)) (hc₁ (e x))
      have hx := hr.2.2.2 X.transpose x (B (e y)) (hc₂ (e y))
      have heq (t : ℝ) :
          B (R (matrixExponentialGL 𝕂 n (t • X)) (e y)) (e x) =
            B (e y) (R (matrixExponentialGL 𝕂 n (t • X.transpose)) (e x)) := by
        have h := hB (matrixExponentialGL 𝕂 n (t • X)) (e y)
          (R (matrixExponentialGL 𝕂 n (t • X.transpose)) (e x))
        have hg : Langlands.GeneralLinear.inverseTranspose n 𝕂
            (matrixExponentialGL 𝕂 n (t • X)) =
              (matrixExponentialGL 𝕂 n (t • X.transpose))⁻¹ := by
          simp
        rw [hg, ← Module.End.mul_apply, ← R.map_mul, inv_mul_cancel, R.map_one] at h
        exact h
      change HasDerivAt (fun t : ℝ =>
        B (R (matrixExponentialGL 𝕂 n (t • X)) (e y)) (e x)) _ 0 at hy
      have heqfun : (fun t : ℝ => B (R (matrixExponentialGL 𝕂 n (t • X)) (e y)) (e x)) =
          (fun t : ℝ => B (e y) (R (matrixExponentialGL 𝕂 n (t • X.transpose)) (e x))) :=
        funext heq
      rw [heqfun] at hy
      exact hy.unique hx
    intro X y x
    induction X using TensorProduct.inductionOn with
    | tmul z X =>
      have h := hreal X y x
      have hz : z ⊗ₜ[ℝ] X = z • (1 ⊗ₜ[ℝ] X) := by
        simpa only [smul_eq_mul, mul_one] using
          (TensorProduct.smul_tmul' z (1 : ℂ) X).symm
      rw [hz]
      simp only [map_smul, LinearMap.smul_apply,
        complexifiedMatrixLieIota_tmul, TensorProduct.tmul_neg, map_neg,
        LinearMap.neg_apply, restrictRealizationPairing_apply]
      rw [h]
      simp
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply, restrictRealizationPairing_apply] at *
      exact add_eq_zero_iff_eq_neg.mpr (by linear_combination hX + hY)

/-- A dense weak realization and a nonzero separately continuous invariant form
supply the exact local pairing predicate. -/
theorem hasNonzeroTransposeGKPairing_of_denseWeakGLRealization
    (hr : IsDenseWeakGLRealization 𝕂 n ρ π R e)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hc₁ : ∀ x : E, Continuous fun y : E => B y x)
    (hc₂ : ∀ y : E, Continuous (B y)) (hne : B ≠ 0)
    (hB : ∀ (g : Langlands.GeneralLinear n 𝕂) (y x : E),
      B (R g y) (R (Langlands.GeneralLinear.inverseTranspose n 𝕂 g) x) = B y x) :
    HasNonzeroTransposeGKPairing 𝕂 n ρ π := by
  exact ⟨restrictRealizationPairing e B,
    isTransposeInvariantGKPairing_restrict 𝕂 n ρ π R e hr B hc₁ hc₂ hB,
    restrictRealizationPairing_ne_zero e hr.2.1 B hc₁ hc₂ hne⟩

end Langlands.Archimedean
