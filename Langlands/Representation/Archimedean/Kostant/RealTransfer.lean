import Langlands.Representation.Archimedean.Kostant.Transport
import Langlands.Representation.Archimedean.Kostant.Matumoto
import Mathlib.RingTheory.MatrixAlgebra

/-!
# From `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` to the one-block product `∏_{Unit} 𝔤𝔩_n(ℂ)`

`toGL n` is the complex Lie algebra isomorphism `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ) ≃ 𝔤𝔩_n(ℂ)`, `z ⊗ X ↦ z X`, with
`𝔤𝔩_n(ℂ)` written as the product over the one-point index type. It is built from Mathlib's
`matrixEquivTensor`; its bracket compatibility holds because the base-changed bracket of
`ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` is the ring commutator.

`isWhittaker_comp`: if `ℓ(π(1 ⊗ X) v) = (i ∑ a_p X_{p,p+1}) ℓ(v)` for real strictly upper
triangular `X` (`IsRealGenericGKModule`), then `ℓ` is a Whittaker functional for
`π ∘ toGL⁻¹` with the coefficients `i a_p`: a complex strictly upper triangular matrix is
`X_re + i X_im` with real strictly upper triangular parts.
-/

noncomputable section

set_option autoImplicit false

-- Entries of tuples of matrices are applied through the `Matrix` definition.
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

theorem realGL_bracket_tmul (a : ℂ) (x : Matrix (Fin n) (Fin n) ℝ)
    (s : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    @Bracket.bracket _ _
      (@LieRing.toBracket _ (inferInstance : LieRing (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)))
      (a ⊗ₜ[ℝ] x) s = a ⊗ₜ[ℝ] x * s - s * a ⊗ₜ[ℝ] x := by
  induction s using TensorProduct.inductionOn with
  | tmul b y =>
    change (a * b) ⊗ₜ[ℝ] ⁅x, y⁆ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Ring.lie_def,
      TensorProduct.tmul_sub, mul_comm b a]
  | add s₁ s₂ h₁ h₂ => rw [LieRing.lie_add, h₁, h₂, mul_add, add_mul]; abel

/-- The base-changed bracket of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` (the Lie ring structure used in
`RealGenericLargeReduction`) is the ring commutator. -/
theorem realGL_bracket_eq (t s : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    @Bracket.bracket _ _
      (@LieRing.toBracket _ (inferInstance : LieRing (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ))) t s =
      t * s - s * t := by
  induction t using TensorProduct.inductionOn with
  | tmul a x => exact realGL_bracket_tmul n a x s
  | add t₁ t₂ h₁ h₂ => rw [add_lie, h₁, h₂, add_mul, mul_add]; abel

theorem matrixEquivTensor_symm_smul (c : ℂ) (t : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    (matrixEquivTensor (Fin n) ℝ ℂ).symm (c • t) = c • (matrixEquivTensor (Fin n) ℝ ℂ).symm t := by
  induction t using TensorProduct.inductionOn with
  | tmul a M =>
    rw [TensorProduct.smul_tmul', matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm,
      smul_smul, smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The isomorphism `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ) ≃ ∏_{Unit} 𝔤𝔩_n(ℂ)`. -/
def toGL : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) ≃ₗ⁅ℂ⁆ GLProd ℂ (fun _ : Unit => n) where
  toFun t := fun _ => (matrixEquivTensor (Fin n) ℝ ℂ).symm t
  invFun X := matrixEquivTensor (Fin n) ℝ ℂ (X ())
  map_add' t s := by funext u; simp [map_add]
  map_smul' c t := by funext u; simp [matrixEquivTensor_symm_smul]
  map_lie' {t s} := by
    funext u
    rw [realGL_bracket_eq, Ring.lie_def]
    simp [map_sub, map_mul]
  left_inv t := (matrixEquivTensor (Fin n) ℝ ℂ).apply_symm_apply t
  right_inv X := by
    funext u
    cases u
    exact (matrixEquivTensor (Fin n) ℝ ℂ).symm_apply_apply (X ())

theorem toGL_apply (t : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (u : Unit) :
    toGL n t u = (matrixEquivTensor (Fin n) ℝ ℂ).symm t := rfl

theorem toGL_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) (u : Unit) :
    toGL n (z ⊗ₜ X) u = z • X.map (algebraMap ℝ ℂ) := rfl

variable {n} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The Whittaker condition of `IsRealGenericGKModule` gives a Whittaker functional for the
transported representation, with coefficients `i a_p`. -/
theorem isWhittaker_comp (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℝ)
    (hW : ∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
      ∀ v : V, ℓ (π (1 ⊗ₜ X) v) =
        (Complex.I * ((∑ i : Fin n, ∑ j : Fin n,
          if (j : ℕ) = i + 1 then a i * X i j else 0 : ℝ) : ℂ)) * ℓ v) :
    IsWhittaker (fun _ : Unit => n) (π.comp (toGL n).symm.toLieHom)
      (fun _ p => Complex.I * a p) ℓ := by
  intro X hX v
  set Xr : Matrix (Fin n) (Fin n) ℝ := (X ()).map Complex.re
  set Xi : Matrix (Fin n) (Fin n) ℝ := (X ()).map Complex.im
  have hXr : ∀ i j : Fin n, (j : ℕ) ≤ i → Xr i j = 0 := by
    intro i j h; simp [Xr, hX () i j h]
  have hXi : ∀ i j : Fin n, (j : ℕ) ≤ i → Xi i j = 0 := by
    intro i j h; simp [Xi, hX () i j h]
  have hsplit : (toGL n).symm X = (1 : ℂ) ⊗ₜ Xr + Complex.I ⊗ₜ Xi := by
    apply (toGL n).injective
    change toGL n ((toGL n).symm X) = toGL n _
    rw [LieEquiv.apply_symm_apply]
    funext u
    cases u
    ext i j
    rw [map_add, Pi.add_apply, toGL_tmul, toGL_tmul]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, one_smul, smul_eq_mul, Xr,
      Xi, Complex.coe_algebraMap]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hI : Complex.I ⊗ₜ[ℝ] Xi = Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] Xi) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [LieHom.comp_apply, LieEquiv.coe_toLieHom, hsplit, map_add, hI, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hW Xr hXr, hW Xi hXi,
    smul_eq_mul]
  simp only [whitChar, Fintype.univ_unit, Finset.sum_singleton]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  split_ifs
  · have hz : X () p q = (Xr p q : ℂ) + (Xi p q : ℂ) * Complex.I := (Complex.re_add_im _).symm
    rw [hz]
    push_cast
    ring
  · simp

end Langlands.Archimedean.Kostant
