import Langlands.Global.RealTensorSplitting
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section
universe u v w
open NumberField Module
open scoped TensorProduct

namespace Langlands.Global.TotallyReal

variable (E : Type u) (A : Type v)
  [Field E] [NumberField E] [IsTotallyReal E]
  [Ring A] [Algebra E A] [Algebra ℚ A] [IsScalarTower ℚ E A]

/-- The actual scalar extension at one real embedding. -/
abbrev At (τ : E →+* ℝ) :=
  letI : Algebra E ℝ := τ.toAlgebra
  ℝ ⊗[E] A

/-- Include the original algebra at one real embedding. -/
def atInclusion (τ : E →+* ℝ) : A →ₐ[ℚ] At E A τ := by
  letI : Algebra E ℝ := τ.toAlgebra
  exact (Algebra.TensorProduct.includeRight : A →ₐ[E] ℝ ⊗[E] A).restrictScalars ℚ

/-- Simultaneous real-place evaluation of the rational scalar extension. -/
def algebraEvaluation : ℝ ⊗[ℚ] A →ₐ[ℝ] ((τ : E →+* ℝ) → At E A τ) :=
  AlgHom.liftEquiv ℚ ℝ A _ (AlgHom.pi (atInclusion E A))

omit [IsTotallyReal E] in
@[simp] theorem algebraEvaluation_tmul (r : ℝ) (a : A) (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    algebraEvaluation E A (r ⊗ₜ[ℚ] a) τ = r ⊗ₜ[E] a := by
  let : Algebra E ℝ := τ.toAlgebra
  change r • ((1 : ℝ) ⊗ₜ[E] a) = r ⊗ₜ[E] a
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {ι : Type w} [Fintype ι] (b : Basis ι E A)

private def transposeCoordinates :
    (ι → (E →+* ℝ) → ℝ) ≃ₗ[ℝ] ((E →+* ℝ) → ι → ℝ) where
  toFun f τ i := f i τ
  invFun f i τ := f τ i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinates reduce the algebra splitting to the field splitting. -/
private def algebraCoordinates :
    ℝ ⊗[ℚ] A ≃ₗ[ℝ] ((E →+* ℝ) → ι → ℝ) := by
  classical
  exact (b.equivFun.restrictScalars ℚ).baseChange ℚ ℝ _ _ ≪≫ₗ
    TensorProduct.piRight ℚ ℝ ℝ (fun _ : ι => E) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ : ι => (tensorEquiv E).toLinearEquiv) ≪≫ₗ
    transposeCoordinates E

private def localCoordinates :
    ((τ : E →+* ℝ) → At E A τ) ≃ₗ[ℝ] ((E →+* ℝ) → ι → ℝ) :=
  LinearEquiv.piCongrRight fun τ => by
    letI : Algebra E ℝ := τ.toAlgebra
    exact (b.baseChange ℝ).equivFun

private theorem algebraCoordinates_tmul (r : ℝ) (a : A) (τ : E →+* ℝ) (i : ι) :
    algebraCoordinates E A b (r ⊗ₜ[ℚ] a) τ i = r * τ (b.repr a i) := by
  simp [algebraCoordinates, transposeCoordinates, Basis.equivFun_apply]

private theorem localCoordinates_evaluation (x : ℝ ⊗[ℚ] A) :
    localCoordinates E A b (algebraEvaluation E A x) = algebraCoordinates E A b x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    funext τ i
    let : Algebra E ℝ := τ.toAlgebra
    simp [localCoordinates, algebraCoordinates_tmul, Basis.equivFun_apply,
      Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm,
      RingHom.algebraMap_toAlgebra]
  | add x y hx hy => simp only [map_add, hx, hy]

include b in
/-- Real-place evaluation is bijective for an algebra with a finite basis over E. -/
theorem algebraEvaluation_bijective :
    Function.Bijective (algebraEvaluation E A) := by
  have h : (algebraEvaluation E A).toLinearMap =
      ((algebraCoordinates E A b).trans (localCoordinates E A b).symm).toLinearMap := by
    apply LinearMap.ext
    intro x
    apply (localCoordinates E A b).injective
    simpa using localCoordinates_evaluation E A b x
  change Function.Bijective (algebraEvaluation E A).toLinearMap
  rw [h]
  exact ((algebraCoordinates E A b).trans (localCoordinates E A b).symm).bijective

/-- The product of all real-place scalar extensions is the rational real scalar extension. -/
def algebraEquiv : ℝ ⊗[ℚ] A ≃ₐ[ℝ] ((τ : E →+* ℝ) → At E A τ) :=
  AlgEquiv.ofBijective (algebraEvaluation E A) (algebraEvaluation_bijective E A b)

@[simp] theorem algebraEquiv_tmul (r : ℝ) (a : A) (τ : E →+* ℝ) :
    letI : Algebra E ℝ := τ.toAlgebra
    algebraEquiv E A b (r ⊗ₜ[ℚ] a) τ = r ⊗ₜ[E] a :=
  algebraEvaluation_tmul E A r a τ

/-- The basis is used to prove bijectivity; the resulting algebra equivalence is independent of it. -/
theorem algebraEquiv_basis_independent {κ : Type*} [Fintype κ] (c : Basis κ E A) :
    algebraEquiv E A b = algebraEquiv E A c := by
  apply AlgEquiv.ext
  intro x
  rfl

end Langlands.Global.TotallyReal
